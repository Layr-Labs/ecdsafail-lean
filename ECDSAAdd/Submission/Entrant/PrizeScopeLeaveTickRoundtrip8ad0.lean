import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPostReadyf724
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRoutedRestore88ff
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
open Arithmetic
inductive Gate where
  | x (t:Wire)
  | cx (a t:Wire)
  | ccx (a b t:Wire)
  | make (a b t:Wire)
  | pop (a b t:Wire)
  deriving DecidableEq

def erase (a b t:Wire):Instr := .measureX t [] [.CZ a b]
def front : Gate→Instr
  | .x t=>.X t
  | .cx a t=>.CX a t
  | .ccx a b t | .make a b t=>.CCX a b t
  | .pop a b t=>erase a b t
def back : Gate→Instr
  | .x t=>.X t
  | .cx a t=>.CX a t
  | .ccx a b t | .pop a b t=>.CCX a b t
  | .make a b t=>erase a b t
def proper : Gate→Bool
  | .x _=>true
  | .cx a t=>decide (a≠t)
  | .ccx a b t | .make a b t | .pop a b t=>decide (a≠t ∧ b≠t)
def ValueOK (s:State):Gate→Prop
  | .pop a b t=>s.basis t=(s.basis a && s.basis b)
  | _=>True
def Fresh (s:State):Gate→Prop
  | .make _ _ t=>s.basis t=false
  | _=>True
def forward (ops:List Gate):Program:=ops.map front
def inverse (ops:List Gate):Program:=(ops.map back).reverse
def transition (g:Gate) (s:State):State:=run [front g] [] s
def Prepared (s:State):List Gate→Prop
  | []=>True
  | g::gs=>ValueOK s g ∧ Prepared (transition g s) gs
theorem no_phase (ops:List Gate) (s:State):(run (forward ops) [] s).phase=s.phase:=by
  induction ops generalizing s with
  | nil=>rfl
  | cons g gs ih=>
    change (run ([front g]++forward gs) [] s).phase=_
    rw [run_append,run_take,List.drop_nil,ih]
    cases g <;> first | rfl | simp [front,erase,run,measureAndCorrect,ECDSAAdd.correct]
theorem head_default (g:Gate) (s:State) (correct:ValueOK s g) (phys:proper g=true) (m:List Bool):
    run [front g] m s=transition g s:=by
  cases g with
  | x|cx|ccx|make=>rfl
  | pop a b t=>
    have dist : a≠t ∧ b≠t := of_decide_eq_true phys
    change s.basis t=(s.basis a && s.basis b) at correct
    cases m with
    | nil=>rfl
    | cons v xs=>
      cases v
      · rfl
      · simp [front,erase,transition,run,measureAndCorrect,correct,ECDSAAdd.correct,writeBit,dist.1,dist.2]
theorem all_prepared (ops:List Gate) (s:State) (phys:∀g∈ops,proper g=true)
    (quiet:∀m,(run (forward ops) m s).phase=s.phase):Prepared s ops:=by
  induction ops generalizing s with
  | nil=>trivial
  | cons g gs ih=>
    have hp:=phys g (by simp)
    have root : ∀m,(run (forward gs) (m.drop (measurementCount [front g])) (run [front g] m s)).phase=s.phase:=by
      intro m
      have eq:=quiet m
      change (run ([front g]++forward gs) m s).phase=_ at eq
      rwa [run_append,run_take] at eq
    have val:ValueOK s g:=by
      cases g with
      | x|cx|ccx|make=>trivial
      | pop a b t=>
        have rel:=root [true]
        change (run (forward gs) [] _).phase=_ at rel
        rw [no_phase] at rel
        have dist : a≠t ∧ b≠t := of_decide_eq_true hp
        change s.basis t=(s.basis a && s.basis b)
        simp [front,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,dist.1,dist.2] at rel
        revert rel;cases s.phase <;> cases s.basis t <;> cases s.basis a <;> cases s.basis b <;> decide
    refine ⟨val,ih _ (fun k h=>phys k (by simp [h])) ?_⟩
    intro m
    let tape:=(List.replicate (measurementCount [front g]) false)++m
    have drop:tape.drop (measurementCount [front g])=m:=by simp [tape]
    have rel:=root tape
    rw [drop,head_default g s val hp] at rel
    have base:(transition g s).phase=s.phase:=by cases g <;> first | rfl | simp [front,transition,erase,run,measureAndCorrect,ECDSAAdd.correct]
    exact rel.trans base.symm
#print axioms all_prepared
end ECDSAAdd.Entrant.StairPacket.GateMirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
open Arithmetic
private theorem reset (f:BasisState) (t:Wire) (b:Bool) :
    writeBit (writeBit f t b) t (f t)=f:=by
  funext q
  by_cases e:q=t <;> simp [writeBit,e]
private theorem restore (s:State) (t:Wire) (b:Bool) :
    (⟨s.phase,writeBit (writeBit s.basis t b) t (s.basis t)⟩:State)=s:=by rw [reset]
theorem undo (g:Gate) (s:State) (hp:proper g=true) (hv:ValueOK s g) (hf:Fresh s g) (m:List Bool):
    run [back g] m (transition g s)=s:=by
  cases g with
  | x t=>
    simp [transition,front,back,run,writeBit]
  | cx a t=>
    have ha:a≠t:=of_decide_eq_true hp
    simp [transition,front,back,run,writeBit,ha]
  | ccx a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    simp [transition,front,back,run,writeBit,ha,hb]
  | pop a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    change s.basis t=(s.basis a && s.basis b) at hv
    simpa [transition,front,back,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ha,hb,hv] using restore s t false
  | make a b t=>
    obtain ⟨ha,hb⟩ : a≠t ∧ b≠t :=of_decide_eq_true hp
    change s.basis t=false at hf
    have h:=restore s t (s.basis a && s.basis b)
    cases e:m.head?.getD false <;>
      simpa [transition,front,back,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ha,hb,hf,e] using h

def Ready (s:State):List Gate→Prop
  | []=>True
  | g::gs=>Fresh s g ∧ Ready (transition g s) gs

theorem invert (ops:List Gate) (s:State) (phys:∀g∈ops,proper g=true)
    (ok:Prepared s ops) (clean:Ready s ops) (m n:List Bool):
    run (inverse ops) n (run (forward ops) m s)=s:=by
  induction ops generalizing s m n with
  | nil=>rfl
  | cons g gs ih=>
    have hp:=phys g (by simp)
    change run ((back g::gs.map back).reverse) n (run ([front g]++forward gs) m s)=s
    rw [List.reverse_cons,run_append,run_append,run_take,run_take]
    rw [head_default g s ok.1 hp]
    rw [show (gs.map back).reverse=inverse gs from rfl,
      ih _ (fun k h=>phys k (by simp [h])) ok.2 clean.2]
    exact undo g s hp ok.1 clean.1 _

end ECDSAAdd.Entrant.StairPacket.GateMirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def target:Gate→Wire
  | .x t | .cx _ t | .ccx _ _ t | .make _ _ t | .pop _ _ t=>t
def WritesZero:Gate→Bool
  | .pop ..=>true
  | _=>false
def NeedsZero:Gate→Bool
  | .make ..=>true
  | _=>false
def zeros (s:State) (ws:List Wire):Prop:=∀q∈ws,s.basis q=false
def before (g:Gate) (ws:List Wire):List Wire:=
  let surviving:=ws.filter (· != target g)
  if NeedsZero g then target g::surviving else surviving
def safe (g:Gate) (ws:List Wire):Bool:=proper g && (WritesZero g || !(ws.contains (target g)))
theorem before_step (g:Gate) (ws:List Wire) (s:State) (hg:safe g ws=true)
    (h:zeros s (before g ws)): proper g=true ∧ Fresh s g ∧ zeros (transition g s) ws:=by
  have hh:=Bool.and_eq_true_iff.mp hg
  refine ⟨hh.1,?_,?_⟩
  · cases g <;> first | trivial | exact h _ (by simp [before,NeedsZero,target])
  · intro q hq
    by_cases eq:q=target g
    · subst q
      have hz:WritesZero g=true:=by simpa [hq] using hh.2
      cases g <;> simp [WritesZero] at hz
      simp [transition,front,run,erase,measureAndCorrect,target,writeBit]
    · have hz:s.basis q=false:=by
        apply h
        cases hneeds:NeedsZero g <;> simp [before,hneeds,hq,eq]
      cases g <;> simp [target] at eq <;>
        simp [transition,front,run,erase,measureAndCorrect,writeBit,eq,hz]
def checked (gs:List Gate) (post:List Wire):Option (List Wire):=
  match gs with
  | []=>some post
  | g::rest=>do
    let ws←checked rest post
    if safe g ws then some (before g ws) else none
theorem checked_sound (gs:List Gate) (s:State) (pre post:List Wire)
    (hc:checked gs post=some pre) (hi:zeros s pre):
    (∀g∈gs,proper g=true) ∧ Ready s gs ∧ zeros (run (forward gs) [] s) post:=by
  induction gs generalizing s pre with
  | nil=>
    simp [checked] at hc
    exact ⟨by simp, trivial,hc ▸ hi⟩
  | cons g gs ih=>
    cases hx:checked gs post with
    | none=>simp [checked,hx] at hc
    | some ws=>
      by_cases hv:safe g ws=true
      · simp [checked,hx,hv] at hc
        subst pre
        obtain ⟨hp,hf,hz⟩:=before_step g ws s hv hi
        obtain ⟨hps,hr,hend⟩:=ih (transition g s) ws hx hz
        refine ⟨fun k hk=>?_,⟨hf,hr⟩,?_⟩
        · rcases List.mem_cons.mp hk with rfl|hh
          · exact hp
          · exact hps k hh
        · change zeros (run ([front g]++forward gs) [] s) post
          rwa [run_append,run_take,List.drop_nil]
      · simp [checked,hx,hv] at hc

theorem check_join (as bs:List Gate) (first middle last:List Wire)
    (ha:checked as middle=some first) (hb:checked bs last=some middle):
    checked (as++bs) last=some first:=by
  induction as generalizing first with
  | nil=>simpa [checked] using hb.trans ha
  | cons g gs ih=>
    cases hh:checked gs middle with
    | none=>simp [checked,hh] at ha
    | some ws=>
      have total:=ih ws hh
      simpa only [List.cons_append,checked,total] using (show (do
        let xs←some ws
        if safe g xs then some (before g xs) else none)=some first by simpa only [checked,hh] using ha)

theorem ready_append (as bs:List Gate) (s:State) (ha:Ready s as)
    (hb:Ready (run (forward as) [] s) bs):Ready s (as++bs):=by
  induction as generalizing s with
  | nil=>exact hb
  | cons g gs ih=>
    refine ⟨ha.1,ih _ ha.2 ?_⟩
    change Ready (run ([front g]++forward gs) [] s) bs at hb
    rwa [run_append,run_take,List.drop_nil] at hb
end ECDSAAdd.Entrant.StairPacket.GateMirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.GateMirror
def Masked (s:State) (mask:Nat):Prop:=∀q,mask.testBit q=true → s.basis q=false
def addBit (m q:Nat):Nat:=m ||| 2^q
def cutBit (m q:Nat):Nat:=if m.testBit q then m ^^^ 2^q else m
theorem add_bit (m t q:Nat):(addBit m t).testBit q=(decide (q=t) || m.testBit q):=by
  rw [addBit,Nat.testBit_or,Nat.testBit_two_pow]
  by_cases h:q=t
  · subst q;simp
  · simp [h,Ne.symm h]
theorem cut_bit (m t q:Nat):(cutBit m t).testBit q=(!decide (q=t) && m.testBit q):=by
  by_cases h:q=t
  · subst q
    cases b:m.testBit t <;> simp [cutBit,b,Nat.testBit_xor]
  · by_cases b:m.testBit t=true <;> simp [cutBit,b,h,Ne.symm h,Nat.testBit_xor]
def bitBefore (g:Gate) (m:Nat):Nat:=if NeedsZero g then addBit m (target g) else cutBit m (target g)
def bitSafe (g:Gate) (m:Nat):Bool:=proper g && (WritesZero g || !m.testBit (target g))
theorem bitStep (g:Gate) (ws:Nat) (s:State) (hg:bitSafe g ws=true)
    (h:Masked s (bitBefore g ws)):proper g=true ∧ Fresh s g ∧ Masked (transition g s) ws:=by
  have hh:=Bool.and_eq_true_iff.mp hg
  refine ⟨hh.1,?_,?_⟩
  · cases g <;> first | trivial | exact h _ (by simp [bitBefore,NeedsZero,target,add_bit])
  · intro q hq
    by_cases eq:q=target g
    · subst q
      have hz:WritesZero g=true:=by simpa [hq] using hh.2
      cases g <;> simp [WritesZero] at hz
      simp [transition,front,run,erase,measureAndCorrect,target,writeBit]
    · have hz:s.basis q=false:=by
        apply h
        cases hneeds:NeedsZero g <;> simp [bitBefore,hneeds,hq,eq,add_bit,cut_bit]
      cases g <;> simp [target] at eq <;>
        simp [transition,front,run,erase,measureAndCorrect,writeBit,eq,hz]
def bitCheck (gs:List Gate) (post:Nat):Option Nat:=
  match gs with
  | []=>some post
  | g::rest=>do
    let ws←bitCheck rest post
    if bitSafe g ws then some (bitBefore g ws) else none
theorem bit_sound (gs:List Gate) (s:State) (pre post:Nat)
    (hc:bitCheck gs post=some pre) (hi:Masked s pre):
    (∀g∈gs,proper g=true) ∧ Ready s gs ∧ Masked (run (forward gs) [] s) post:=by
  induction gs generalizing s pre with
  | nil=>
    simp [bitCheck] at hc
    exact ⟨by simp, trivial,hc ▸ hi⟩
  | cons g gs ih=>
    cases hx:bitCheck gs post with
    | none=>simp [bitCheck,hx] at hc
    | some ws=>
      by_cases hv:bitSafe g ws=true
      · simp [bitCheck,hx,hv] at hc
        subst pre
        obtain ⟨hp,hf,hz⟩:=bitStep g ws s hv hi
        obtain ⟨hps,hr,hend⟩:=ih (transition g s) ws hx hz
        refine ⟨fun k hk=>?_,⟨hf,hr⟩,?_⟩
        · rcases List.mem_cons.mp hk with rfl|hh
          · exact hp
          · exact hps k hh
        · change Masked (run ([front g]++forward gs) [] s) post
          rwa [run_append,run_take,List.drop_nil]
      · simp [bitCheck,hx,hv] at hc

theorem bit_join (as bs:List Gate) (first middle last:Nat)
    (ha:bitCheck as middle=some first) (hb:bitCheck bs last=some middle):
    bitCheck (as++bs) last=some first:=by
  induction as generalizing first with
  | nil=>simpa [bitCheck] using hb.trans ha
  | cons g gs ih=>
    cases hh:bitCheck gs middle with
    | none=>simp [bitCheck,hh] at ha
    | some ws=>
      have total:=ih ws hh
      simpa only [List.cons_append,bitCheck,total] using (show (do
        let xs←some ws
        if bitSafe g xs then some (bitBefore g xs) else none)=some first by simpa only [bitCheck,hh] using ha)

theorem subMask {s:State} {small big:Nat} (test:small &&& big=small) (h:Masked s big):Masked s small:=by
  intro q hq
  have v:=congrArg (fun n:Nat=>n.testBit q) test
  simp [Nat.testBit_and,hq] at v
  exact h q v
theorem bothMasks {s:State} {a b:Nat} (ha:Masked s a) (hb:Masked s b):Masked s (a ||| b):=by
  intro q hq
  rw [Nat.testBit_or,Bool.or_eq_true] at hq
  exact hq.elim (ha q) (hb q)
def interval (lo width:Nat):Nat:=(2^width-1) <<< lo
theorem fromRange {s:State} {lo width:Nat} (h:∀q,lo≤q→q<lo+width→s.basis q=false):
    Masked s (interval lo width):=by
  intro q hq
  simp only [interval,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one] at hq
  apply h <;> simp_all
  omega
def maskSites (ws:List Wire):Nat:=ws.foldr (fun q m=>addBit m q) 0
theorem fromList {s:State} {ws:List Wire} (h:zeros s ws):Masked s (maskSites ws):=by
  induction ws with
  | nil=>intro q hq;simp [maskSites] at hq
  | cons a as ih=>
    intro q hq
    change (addBit (maskSites as) a).testBit q=true at hq
    rw [add_bit,Bool.or_eq_true] at hq
    rcases hq with eq|hv
    · exact h q (by simp [of_decide_eq_true eq])
    · exact ih (fun k hh=>h k (by simp [hh])) q hv
theorem fwAppend (a b:List Gate):forward (a++b)=forward a ++ forward b:=List.map_append
theorem bwAppend (a b:List Gate):inverse (a++b)=inverse b ++ inverse a:=by
  simp only [inverse,List.map_append,List.reverse_append]
theorem fwNil:forward []=[]:=rfl
theorem bwNil:inverse []=[]:=rfl
end ECDSAAdd.Entrant.StairPacket.GateMirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
private def block2847 : List Gate := [
  .x 1269,
  .make 1725 1269 1556,
  .x 1270,
  .make 1556 1270 1559,
  .x 1271,
  .make 1559 1271 1560,
  .x 1272,
  .make 1560 1272 1561,
  .x 1273,
  .make 1561 1273 1562,
  .cx 1562 1722,
  .pop 1561 1273 1562,
  .x 1273,
  .pop 1560 1272 1561,
  .x 1272,
  .pop 1559 1271 1560,
  .x 1271,
  .pop 1556 1270 1559,
  .x 1270,
  .pop 1725 1269 1556,
  .x 1269,
  .cx 956 941,
  .cx 941 956,
  .cx 956 941,
  .cx 957 942,
  .cx 942 957,
  .cx 957 942,
  .cx 958 943,
  .cx 943 958,
  .cx 958 943,
  .cx 959 944,
  .cx 944 959,
  .cx 959 944]
private def block2880 : List Gate := [
  .cx 960 945,
  .cx 945 960,
  .cx 960 945,
  .cx 961 946,
  .cx 946 961,
  .cx 961 946,
  .cx 962 947]
private def block2887 : List Gate := [
  .cx 947 962,
  .cx 962 947,
  .cx 963 948,
  .cx 948 963,
  .cx 963 948,
  .cx 964 949,
  .cx 949 964,
  .cx 964 949,
  .cx 965 950,
  .cx 950 965,
  .cx 965 950,
  .cx 966 951,
  .cx 951 966,
  .cx 966 951,
  .cx 967 952,
  .cx 952 967,
  .cx 967 952]
private def block2904 : List Gate := [
  .cx 968 953,
  .cx 953 968,
  .cx 968 953,
  .cx 969 954,
  .cx 954 969,
  .cx 969 954,
  .cx 970 955,
  .cx 955 970,
  .cx 970 955,
  .cx 971 956,
  .cx 956 971,
  .cx 971 956,
  .cx 972 957,
  .cx 957 972,
  .cx 972 957,
  .cx 973 958,
  .cx 958 973,
  .cx 973 958,
  .cx 974 959,
  .cx 959 974,
  .cx 974 959,
  .cx 975 960,
  .cx 960 975]
private def block2927 : List Gate := [
  .cx 975 960,
  .cx 976 961,
  .cx 961 976,
  .cx 976 961,
  .cx 977 962,
  .cx 962 977,
  .cx 977 962,
  .cx 978 963,
  .cx 963 978,
  .cx 978 963,
  .cx 979 964,
  .cx 964 979,
  .cx 979 964,
  .cx 980 965,
  .cx 965 980,
  .cx 980 965,
  .cx 981 966,
  .cx 966 981,
  .cx 981 966,
  .cx 982 967,
  .cx 967 982,
  .cx 982 967,
  .cx 983 968,
  .cx 968 983,
  .cx 983 968,
  .cx 984 969,
  .cx 969 984,
  .cx 984 969,
  .cx 985 970,
  .cx 970 985,
  .cx 985 970,
  .cx 986 971,
  .cx 971 986,
  .cx 986 971,
  .cx 987 972,
  .cx 972 987,
  .cx 987 972,
  .cx 988 973,
  .cx 973 988,
  .cx 988 973]
private def block2967 : List Gate := [
  .cx 989 974,
  .cx 974 989,
  .cx 989 974,
  .cx 990 975,
  .cx 975 990,
  .cx 990 975,
  .cx 991 976,
  .cx 976 991,
  .cx 991 976]
private def block2976 : List Gate := [
  .cx 992 977,
  .cx 977 992,
  .cx 992 977,
  .cx 993 978,
  .cx 978 993,
  .cx 993 978,
  .cx 994 979,
  .cx 979 994,
  .cx 994 979,
  .cx 995 980,
  .cx 980 995,
  .cx 995 980,
  .cx 996 981,
  .cx 981 996,
  .cx 996 981,
  .cx 997 982,
  .cx 982 997,
  .cx 997 982,
  .cx 998 983,
  .cx 983 998,
  .cx 998 983,
  .cx 999 984,
  .cx 984 999,
  .cx 999 984]
private def block3000 : List Gate := [
  .cx 1000 985,
  .cx 985 1000,
  .cx 1000 985,
  .cx 1001 986,
  .cx 986 1001,
  .cx 1001 986,
  .cx 1002 987]
private def block3007 : List Gate := [
  .cx 987 1002,
  .cx 1002 987,
  .cx 1003 988,
  .cx 988 1003,
  .cx 1003 988,
  .cx 1004 989,
  .cx 989 1004,
  .cx 1004 989,
  .cx 1005 990,
  .cx 990 1005,
  .cx 1005 990,
  .cx 1006 991,
  .cx 991 1006,
  .cx 1006 991,
  .cx 1007 992,
  .cx 992 1007,
  .cx 1007 992,
  .cx 1008 993,
  .cx 993 1008,
  .cx 1008 993,
  .cx 1009 994,
  .cx 994 1009,
  .cx 1009 994,
  .cx 1010 995,
  .cx 995 1010,
  .cx 1010 995,
  .cx 1011 996,
  .cx 996 1011,
  .cx 1011 996,
  .cx 1012 997,
  .cx 997 1012,
  .cx 1012 997,
  .cx 1013 998,
  .cx 998 1013,
  .cx 1013 998,
  .cx 1014 999,
  .cx 999 1014,
  .cx 1014 999,
  .cx 1015 1000,
  .cx 1000 1015]
private def block3047 : List Gate := [
  .cx 1015 1000,
  .cx 1016 1001,
  .cx 1001 1016,
  .cx 1016 1001,
  .cx 1017 1002,
  .cx 1002 1017,
  .cx 1017 1002,
  .cx 1018 1003,
  .cx 1003 1018,
  .cx 1018 1003,
  .cx 1019 1004,
  .cx 1004 1019,
  .cx 1019 1004,
  .cx 1020 1005,
  .cx 1005 1020,
  .cx 1020 1005,
  .cx 1021 1006,
  .cx 1006 1021,
  .cx 1021 1006,
  .cx 1022 1007,
  .cx 1007 1022,
  .cx 1022 1007,
  .cx 1023 1008,
  .cx 1008 1023,
  .cx 1023 1008]
private def block3072 : List Gate := [
  .cx 1024 1009,
  .cx 1009 1024,
  .cx 1024 1009,
  .cx 1025 1010,
  .cx 1010 1025,
  .cx 1025 1010,
  .cx 1026 1011,
  .cx 1011 1026,
  .cx 1026 1011,
  .cx 1027 1012,
  .cx 1012 1027,
  .cx 1027 1012,
  .cx 1028 1013,
  .cx 1013 1028,
  .cx 1028 1013]
private def block3087 : List Gate := [
  .cx 1029 1014,
  .cx 1014 1029,
  .cx 1029 1014,
  .cx 1030 1015,
  .cx 1015 1030,
  .cx 1030 1015,
  .cx 1031 1016,
  .cx 1016 1031,
  .cx 1031 1016]
private def block3096 : List Gate := [
  .cx 1032 1017,
  .cx 1017 1032,
  .cx 1032 1017,
  .cx 1033 1018,
  .cx 1018 1033,
  .cx 1033 1018,
  .cx 1034 1019,
  .cx 1019 1034,
  .cx 1034 1019,
  .cx 1035 1020,
  .cx 1020 1035,
  .cx 1035 1020,
  .cx 1036 1021,
  .cx 1021 1036,
  .cx 1036 1021,
  .cx 1037 1022,
  .cx 1022 1037,
  .cx 1037 1022,
  .cx 1038 1023,
  .cx 1023 1038,
  .cx 1038 1023,
  .cx 1039 1024,
  .cx 1024 1039,
  .cx 1039 1024,
  .cx 1040 1025,
  .cx 1025 1040,
  .cx 1040 1025,
  .cx 1041 1026,
  .cx 1026 1041,
  .cx 1041 1026,
  .cx 1042 1027]
private def block3127 : List Gate := [
  .cx 1027 1042,
  .cx 1042 1027,
  .cx 1598 1028,
  .cx 1028 1598,
  .cx 1598 1028,
  .cx 1599 1029,
  .cx 1029 1599,
  .cx 1599 1029,
  .cx 1600 1030,
  .cx 1030 1600,
  .cx 1600 1030,
  .cx 1601 1031,
  .cx 1031 1601,
  .cx 1601 1031,
  .cx 1602 1032,
  .cx 1032 1602,
  .cx 1602 1032,
  .cx 1603 1033,
  .cx 1033 1603,
  .cx 1603 1033,
  .cx 1604 1034,
  .cx 1034 1604,
  .cx 1604 1034,
  .cx 1605 1035,
  .cx 1035 1605,
  .cx 1605 1035,
  .cx 1606 1036,
  .cx 1036 1606,
  .cx 1606 1036,
  .cx 1607 1037,
  .cx 1037 1607,
  .cx 1607 1037,
  .cx 1608 1038,
  .cx 1038 1608,
  .cx 1608 1038,
  .cx 1609 1039,
  .cx 1039 1609,
  .cx 1609 1039,
  .cx 1610 1040,
  .cx 1040 1610]
private def block3167 : List Gate := [
  .cx 1610 1040]
private def block3168 : List Gate := [
  .cx 1611 1041,
  .cx 1041 1611,
  .cx 1611 1041,
  .cx 1612 1042,
  .cx 1042 1612,
  .cx 1612 1042,
  .cx 1557 1713,
  .cx 1713 1557,
  .cx 1557 1713,
  .cx 1558 1714,
  .cx 1714 1558,
  .cx 1558 1714,
  .cx 1723 1715,
  .cx 1715 1723,
  .cx 1723 1715,
  .cx 1721 1716,
  .cx 1716 1721,
  .cx 1721 1716,
  .cx 1725 1717,
  .cx 1717 1725,
  .cx 1725 1717,
  .cx 1724 1718,
  .cx 1718 1724,
  .cx 1724 1718]
private theorem check3168 : bitCheck block3168 0 = some 0 := by decide +kernel
private def suffix3168 := block3168 ++ ([]:List Gate)
private theorem valid3168 : bitCheck suffix3168 0 = some 0 := bit_join block3168 ([]:List Gate) _ 0 _ check3168 rfl
private theorem check3167 : bitCheck block3167 0 = some 0 := by decide +kernel
private def suffix3167 := block3167 ++ suffix3168
private theorem valid3167 : bitCheck suffix3167 0 = some 0 := bit_join block3167 suffix3168 _ 0 _ check3167 valid3168
private theorem check3127 : bitCheck block3127 0 = some 0 := by decide +kernel
private def suffix3127 := block3127 ++ suffix3167
private theorem valid3127 : bitCheck suffix3127 0 = some 0 := bit_join block3127 suffix3167 _ 0 _ check3127 valid3167
private theorem check3096 : bitCheck block3096 0 = some 0 := by decide +kernel
private def suffix3096 := block3096 ++ suffix3127
private theorem valid3096 : bitCheck suffix3096 0 = some 0 := bit_join block3096 suffix3127 _ 0 _ check3096 valid3127
private theorem check3087 : bitCheck block3087 0 = some 0 := by decide +kernel
private def suffix3087 := block3087 ++ suffix3096
private theorem valid3087 : bitCheck suffix3087 0 = some 0 := bit_join block3087 suffix3096 _ 0 _ check3087 valid3096
private theorem check3072 : bitCheck block3072 0 = some 0 := by decide +kernel
private def suffix3072 := block3072 ++ suffix3087
private theorem valid3072 : bitCheck suffix3072 0 = some 0 := bit_join block3072 suffix3087 _ 0 _ check3072 valid3087
private theorem check3047 : bitCheck block3047 0 = some 0 := by decide +kernel
private def suffix3047 := block3047 ++ suffix3072
private theorem valid3047 : bitCheck suffix3047 0 = some 0 := bit_join block3047 suffix3072 _ 0 _ check3047 valid3072
private theorem check3007 : bitCheck block3007 0 = some 0 := by decide +kernel
private def suffix3007 := block3007 ++ suffix3047
private theorem valid3007 : bitCheck suffix3007 0 = some 0 := bit_join block3007 suffix3047 _ 0 _ check3007 valid3047
private theorem check3000 : bitCheck block3000 0 = some 0 := by decide +kernel
private def suffix3000 := block3000 ++ suffix3007
private theorem valid3000 : bitCheck suffix3000 0 = some 0 := bit_join block3000 suffix3007 _ 0 _ check3000 valid3007
private theorem check2976 : bitCheck block2976 0 = some 0 := by decide +kernel
private def suffix2976 := block2976 ++ suffix3000
private theorem valid2976 : bitCheck suffix2976 0 = some 0 := bit_join block2976 suffix3000 _ 0 _ check2976 valid3000
private theorem check2967 : bitCheck block2967 0 = some 0 := by decide +kernel
private def suffix2967 := block2967 ++ suffix2976
private theorem valid2967 : bitCheck suffix2967 0 = some 0 := bit_join block2967 suffix2976 _ 0 _ check2967 valid2976
private theorem check2927 : bitCheck block2927 0 = some 0 := by decide +kernel
private def suffix2927 := block2927 ++ suffix2967
private theorem valid2927 : bitCheck suffix2927 0 = some 0 := bit_join block2927 suffix2967 _ 0 _ check2927 valid2967
private theorem check2904 : bitCheck block2904 0 = some 0 := by decide +kernel
private def suffix2904 := block2904 ++ suffix2927
private theorem valid2904 : bitCheck suffix2904 0 = some 0 := bit_join block2904 suffix2927 _ 0 _ check2904 valid2927
private theorem check2887 : bitCheck block2887 0 = some 0 := by decide +kernel
private def suffix2887 := block2887 ++ suffix2904
private theorem valid2887 : bitCheck suffix2887 0 = some 0 := bit_join block2887 suffix2904 _ 0 _ check2887 valid2904
private theorem check2880 : bitCheck block2880 0 = some 0 := by decide +kernel
private def suffix2880 := block2880 ++ suffix2887
private theorem valid2880 : bitCheck suffix2880 0 = some 0 := bit_join block2880 suffix2887 _ 0 _ check2880 valid2887
private theorem check2847 : bitCheck block2847 0 = some (0x79 <<< 1556) := by decide +kernel
private def suffix2847 := block2847 ++ suffix2880
private theorem valid2847 : bitCheck suffix2847 0 = some (0x79 <<< 1556) := bit_join block2847 suffix2880 _ 0 _ check2847 valid2880
private def group2 := suffix2847
private theorem cert2 : bitCheck group2 0 = some (0x79 <<< 1556) := valid2847
private def block2260 : List Gate := [
  .ccx 1556 401 931,
  .ccx 1556 402 932,
  .ccx 1556 403 933,
  .ccx 1556 404 934,
  .ccx 1556 405 935,
  .ccx 1556 406 936,
  .ccx 1556 407 937,
  .ccx 1556 408 938,
  .ccx 1556 409 939,
  .ccx 1556 410 940,
  .x 931,
  .x 932,
  .x 933,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .make 931 1558 1559,
  .make 932 1559 1560,
  .make 933 1560 1561,
  .make 934 1561 1562,
  .make 935 1562 1563,
  .make 936 1563 1564,
  .make 937 1564 1565,
  .make 938 1565 1566,
  .make 939 1566 1567,
  .cx 1567 940,
  .pop 939 1566 1567,
  .cx 1566 939,
  .pop 938 1565 1566,
  .cx 1565 938,
  .pop 937 1564 1565,
  .cx 1564 937,
  .pop 936 1563 1564,
  .cx 1563 936,
  .pop 935 1562 1563,
  .cx 1562 935]
private def block2300 : List Gate := [
  .pop 934 1561 1562,
  .cx 1561 934,
  .pop 933 1560 1561,
  .cx 1560 933]
private def block2304 : List Gate := [
  .pop 932 1559 1560,
  .cx 1559 932,
  .pop 931 1558 1559,
  .cx 1558 931,
  .x 931,
  .x 932,
  .x 933,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .pop 930 1557 1558,
  .cx 400 1557,
  .x 1557,
  .make 408 409 1558,
  .x 1558,
  .x 410,
  .x 956,
  .x 957,
  .x 958,
  .x 959]
private def block2328 : List Gate := [
  .x 960,
  .x 961,
  .x 962,
  .x 963,
  .x 964,
  .x 965,
  .x 966,
  .x 967,
  .x 968,
  .x 969,
  .x 970,
  .x 971]
private def block2340 : List Gate := [
  .x 972,
  .x 973,
  .x 974,
  .x 975,
  .x 976,
  .x 977,
  .x 978,
  .x 979,
  .x 980,
  .x 981,
  .x 982,
  .x 983,
  .x 984,
  .x 985,
  .x 986,
  .x 987,
  .x 988,
  .x 989,
  .x 990,
  .x 991,
  .x 992,
  .x 993,
  .x 994,
  .x 995,
  .x 996,
  .x 997,
  .x 998,
  .x 999,
  .x 1000,
  .x 1001,
  .x 1002,
  .x 1003,
  .x 1004,
  .x 1005,
  .x 1006,
  .x 1007,
  .x 1008,
  .x 1009,
  .x 1010,
  .x 1011]
private def block2380 : List Gate := [
  .x 1012,
  .x 1013,
  .x 1014,
  .x 1015,
  .x 1016,
  .x 1017,
  .x 1018,
  .x 1019,
  .x 1020,
  .x 1021,
  .x 1022,
  .x 1023,
  .x 1024,
  .x 1025,
  .x 1026,
  .x 1027,
  .x 1028,
  .x 1029,
  .x 1030,
  .x 1031]
private def block2400 : List Gate := [
  .x 1032,
  .x 1033,
  .x 1034,
  .x 1035,
  .x 1036,
  .x 1037,
  .x 1038,
  .x 1039,
  .x 1040,
  .x 1041,
  .x 1042,
  .x 1598,
  .x 1599,
  .x 1600,
  .x 1601,
  .x 1602,
  .x 1603,
  .x 1604,
  .x 1605,
  .x 1606]
private def block2420 : List Gate := [
  .x 1607,
  .x 1608,
  .x 1609,
  .x 1610]
private def block2424 : List Gate := [
  .x 1611,
  .x 1612,
  .make 1558 410 1559,
  .make 1559 956 1560,
  .make 1560 957 1561,
  .make 1561 958 1562,
  .make 1562 959 1563,
  .make 1563 960 1564,
  .make 1564 961 1565,
  .make 1565 962 1566,
  .make 1566 963 1567,
  .make 1567 964 1568,
  .make 1568 965 1569,
  .make 1569 966 1570,
  .make 1570 967 1571,
  .make 1571 968 1572,
  .make 1572 969 1573,
  .make 1573 970 1574,
  .make 1574 971 1575,
  .make 1575 972 1576,
  .make 1576 973 1577,
  .make 1577 974 1578,
  .make 1578 975 1579,
  .make 1579 976 1580,
  .make 1580 977 1581,
  .make 1581 978 1582,
  .make 1582 979 1583,
  .make 1583 980 1584,
  .make 1584 981 1585,
  .make 1585 982 1586,
  .make 1586 983 1587,
  .make 1587 984 1588,
  .make 1588 985 1589,
  .make 1589 986 1590,
  .make 1590 987 1591,
  .make 1591 988 1592]
private def block2460 : List Gate := [
  .make 1592 989 1593,
  .make 1593 990 1594,
  .make 1594 991 1595,
  .make 1595 992 1596,
  .make 1596 993 1597,
  .make 1597 994 1613,
  .make 1613 995 1614,
  .make 1614 996 1615,
  .make 1615 997 1616,
  .make 1616 998 1617,
  .make 1617 999 1618,
  .make 1618 1000 1619,
  .make 1619 1001 1620,
  .make 1620 1002 1621,
  .make 1621 1003 1622,
  .make 1622 1004 1623,
  .make 1623 1005 1624,
  .make 1624 1006 1625,
  .make 1625 1007 1626,
  .make 1626 1008 1627,
  .make 1627 1009 1628,
  .make 1628 1010 1629,
  .make 1629 1011 1630,
  .make 1630 1012 1631,
  .make 1631 1013 1632,
  .make 1632 1014 1633,
  .make 1633 1015 1634,
  .make 1634 1016 1635,
  .make 1635 1017 1636,
  .make 1636 1018 1637,
  .make 1637 1019 1638,
  .make 1638 1020 1639,
  .make 1639 1021 1640,
  .make 1640 1022 1641,
  .make 1641 1023 1642,
  .make 1642 1024 1643]
private def block2496 : List Gate := [
  .make 1643 1025 1644,
  .make 1644 1026 1645,
  .make 1645 1027 1646,
  .make 1646 1028 1647]
private def block2500 : List Gate := [
  .make 1647 1029 1648,
  .make 1648 1030 1649,
  .make 1649 1031 1650,
  .make 1650 1032 1651,
  .make 1651 1033 1652,
  .make 1652 1034 1653,
  .make 1653 1035 1654,
  .make 1654 1036 1655,
  .make 1655 1037 1656,
  .make 1656 1038 1657,
  .make 1657 1039 1658,
  .make 1658 1040 1659,
  .make 1659 1041 1660,
  .make 1660 1042 1661,
  .make 1661 1598 1662,
  .make 1662 1599 1663,
  .make 1663 1600 1664,
  .make 1664 1601 1665,
  .make 1665 1602 1666,
  .make 1666 1603 1667]
private def block2520 : List Gate := [
  .make 1667 1604 1668,
  .make 1668 1605 1669,
  .make 1669 1606 1670,
  .make 1670 1607 1671,
  .make 1671 1608 1672,
  .make 1672 1609 1673,
  .make 1673 1610 1674,
  .make 1674 1611 1675,
  .make 1675 1612 1676,
  .cx 1676 1557,
  .x 1557,
  .pop 1675 1612 1676,
  .pop 1674 1611 1675,
  .pop 1673 1610 1674,
  .pop 1672 1609 1673,
  .pop 1671 1608 1672,
  .pop 1670 1607 1671,
  .pop 1669 1606 1670,
  .pop 1668 1605 1669,
  .pop 1667 1604 1668]
private def block2540 : List Gate := [
  .pop 1666 1603 1667,
  .pop 1665 1602 1666,
  .pop 1664 1601 1665,
  .pop 1663 1600 1664,
  .pop 1662 1599 1663,
  .pop 1661 1598 1662,
  .pop 1660 1042 1661,
  .pop 1659 1041 1660,
  .pop 1658 1040 1659,
  .pop 1657 1039 1658,
  .pop 1656 1038 1657,
  .pop 1655 1037 1656,
  .pop 1654 1036 1655,
  .pop 1653 1035 1654,
  .pop 1652 1034 1653,
  .pop 1651 1033 1652,
  .pop 1650 1032 1651,
  .pop 1649 1031 1650,
  .pop 1648 1030 1649,
  .pop 1647 1029 1648,
  .pop 1646 1028 1647,
  .pop 1645 1027 1646,
  .pop 1644 1026 1645,
  .pop 1643 1025 1644,
  .pop 1642 1024 1643,
  .pop 1641 1023 1642,
  .pop 1640 1022 1641,
  .pop 1639 1021 1640,
  .pop 1638 1020 1639,
  .pop 1637 1019 1638,
  .pop 1636 1018 1637,
  .pop 1635 1017 1636,
  .pop 1634 1016 1635,
  .pop 1633 1015 1634,
  .pop 1632 1014 1633,
  .pop 1631 1013 1632,
  .pop 1630 1012 1631,
  .pop 1629 1011 1630,
  .pop 1628 1010 1629,
  .pop 1627 1009 1628]
private def block2580 : List Gate := [
  .pop 1626 1008 1627,
  .pop 1625 1007 1626,
  .pop 1624 1006 1625,
  .pop 1623 1005 1624,
  .pop 1622 1004 1623,
  .pop 1621 1003 1622,
  .pop 1620 1002 1621,
  .pop 1619 1001 1620,
  .pop 1618 1000 1619,
  .pop 1617 999 1618,
  .pop 1616 998 1617,
  .pop 1615 997 1616]
private def block2592 : List Gate := [
  .pop 1614 996 1615,
  .pop 1613 995 1614,
  .pop 1597 994 1613,
  .pop 1596 993 1597,
  .pop 1595 992 1596,
  .pop 1594 991 1595,
  .pop 1593 990 1594,
  .pop 1592 989 1593,
  .pop 1591 988 1592,
  .pop 1590 987 1591,
  .pop 1589 986 1590,
  .pop 1588 985 1589,
  .pop 1587 984 1588,
  .pop 1586 983 1587,
  .pop 1585 982 1586,
  .pop 1584 981 1585,
  .pop 1583 980 1584,
  .pop 1582 979 1583,
  .pop 1581 978 1582,
  .pop 1580 977 1581,
  .pop 1579 976 1580,
  .pop 1578 975 1579,
  .pop 1577 974 1578,
  .pop 1576 973 1577]
private def block2616 : List Gate := [
  .pop 1575 972 1576,
  .pop 1574 971 1575,
  .pop 1573 970 1574,
  .pop 1572 969 1573]
private def block2620 : List Gate := [
  .pop 1571 968 1572,
  .pop 1570 967 1571,
  .pop 1569 966 1570,
  .pop 1568 965 1569,
  .pop 1567 964 1568,
  .pop 1566 963 1567,
  .pop 1565 962 1566,
  .pop 1564 961 1565,
  .pop 1563 960 1564,
  .pop 1562 959 1563,
  .pop 1561 958 1562,
  .pop 1560 957 1561,
  .pop 1559 956 1560,
  .pop 1558 410 1559,
  .x 1612,
  .x 1611,
  .x 1610,
  .x 1609,
  .x 1608,
  .x 1607,
  .x 1606,
  .x 1605,
  .x 1604,
  .x 1603,
  .x 1602,
  .x 1601,
  .x 1600,
  .x 1599,
  .x 1598,
  .x 1042,
  .x 1041,
  .x 1040,
  .x 1039,
  .x 1038,
  .x 1037,
  .x 1036,
  .x 1035,
  .x 1034,
  .x 1033,
  .x 1032]
private def block2660 : List Gate := [
  .x 1031,
  .x 1030,
  .x 1029,
  .x 1028,
  .x 1027,
  .x 1026,
  .x 1025,
  .x 1024,
  .x 1023,
  .x 1022,
  .x 1021,
  .x 1020,
  .x 1019,
  .x 1018,
  .x 1017,
  .x 1016,
  .x 1015,
  .x 1014,
  .x 1013,
  .x 1012,
  .x 1011,
  .x 1010,
  .x 1009,
  .x 1008,
  .x 1007,
  .x 1006,
  .x 1005,
  .x 1004]
private def block2688 : List Gate := [
  .x 1003,
  .x 1002,
  .x 1001,
  .x 1000,
  .x 999,
  .x 998,
  .x 997,
  .x 996,
  .x 995,
  .x 994,
  .x 993,
  .x 992]
private def block2700 : List Gate := [
  .x 991,
  .x 990,
  .x 989,
  .x 988,
  .x 987,
  .x 986,
  .x 985,
  .x 984,
  .x 983,
  .x 982,
  .x 981,
  .x 980]
private def block2712 : List Gate := [
  .x 979,
  .x 978,
  .x 977,
  .x 976,
  .x 975,
  .x 974,
  .x 973,
  .x 972,
  .x 971,
  .x 970,
  .x 969,
  .x 968,
  .x 967,
  .x 966,
  .x 965,
  .x 964,
  .x 963,
  .x 962,
  .x 961,
  .x 960,
  .x 959,
  .x 958,
  .x 957,
  .x 956,
  .x 410,
  .x 1558,
  .pop 408 409 1558,
  .make 1556 1557 1558]
private def block2740 : List Gate := [
  .x 1558,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .make 1558 930 1559,
  .make 1559 931 1560,
  .make 1560 932 1561,
  .make 1561 933 1562,
  .make 1562 934 1563,
  .make 1563 935 1564,
  .make 1564 936 1565,
  .make 1565 937 1566,
  .make 1566 938 1567,
  .make 1567 939 1568,
  .make 1568 940 1569,
  .cx 1569 1556,
  .x 1556,
  .pop 1568 940 1569,
  .pop 1567 939 1568,
  .pop 1566 938 1567,
  .pop 1565 937 1566,
  .pop 1564 936 1565,
  .pop 1563 935 1564,
  .pop 1562 934 1563,
  .pop 1561 933 1562,
  .pop 1560 932 1561,
  .pop 1559 931 1560,
  .pop 1558 930 1559,
  .x 940,
  .x 939,
  .x 938,
  .x 937]
private def block2780 : List Gate := [
  .x 936,
  .x 935,
  .x 934,
  .x 933]
private def block2784 : List Gate := [
  .x 932,
  .x 931,
  .x 930,
  .x 1558,
  .x 241,
  .x 242,
  .x 243,
  .x 244,
  .x 245,
  .x 246,
  .x 247,
  .x 248,
  .x 249,
  .x 250,
  .x 251,
  .x 252,
  .x 253,
  .x 254,
  .x 255,
  .cx 1723 930,
  .cx 1723 931,
  .cx 1723 932,
  .cx 1723 933,
  .cx 1723 934]
private def block2808 : List Gate := [
  .cx 1723 935,
  .cx 1723 936,
  .cx 1723 937,
  .cx 1723 938,
  .cx 1723 939,
  .cx 1723 940,
  .cx 400 930,
  .ccx 255 930 400,
  .cx 400 930,
  .cx 401 931,
  .ccx 255 931 401,
  .cx 401 931]
private def block2820 : List Gate := [
  .cx 402 932,
  .ccx 255 932 402,
  .cx 402 932,
  .cx 403 933,
  .ccx 255 933 403,
  .cx 403 933,
  .cx 404 934,
  .ccx 255 934 404,
  .cx 404 934,
  .cx 405 935,
  .ccx 255 935 405,
  .cx 405 935,
  .cx 406 936,
  .ccx 255 936 406,
  .cx 406 936,
  .cx 407 937,
  .ccx 255 937 407,
  .cx 407 937,
  .cx 408 938,
  .ccx 255 938 408,
  .cx 408 938,
  .cx 409 939,
  .ccx 255 939 409,
  .cx 409 939,
  .cx 410 940,
  .ccx 255 940 410,
  .cx 410 940]
private theorem check2820 : bitCheck block2820 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2820 := block2820 ++ ([]:List Gate)
private theorem valid2820 : bitCheck suffix2820 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2820 ([]:List Gate) _ (0x78 <<< 1556) _ check2820 rfl
private theorem check2808 : bitCheck block2808 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2808 := block2808 ++ suffix2820
private theorem valid2808 : bitCheck suffix2808 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2808 suffix2820 _ (0x78 <<< 1556) _ check2808 valid2820
private theorem check2784 : bitCheck block2784 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2784 := block2784 ++ suffix2808
private theorem valid2784 : bitCheck suffix2784 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2784 suffix2808 _ (0x78 <<< 1556) _ check2784 valid2808
private theorem check2780 : bitCheck block2780 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2780 := block2780 ++ suffix2784
private theorem valid2780 : bitCheck suffix2780 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2780 suffix2784 _ (0x78 <<< 1556) _ check2780 valid2784
private theorem check2740 : bitCheck block2740 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2740 := block2740 ++ suffix2780
private theorem valid2740 : bitCheck suffix2740 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2740 suffix2780 _ (0x78 <<< 1556) _ check2740 valid2780
private theorem check2712 : bitCheck block2712 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2712 := block2712 ++ suffix2740
private theorem valid2712 : bitCheck suffix2712 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2712 suffix2740 _ (0x3ff8 <<< 1556) _ check2712 valid2740
private theorem check2700 : bitCheck block2700 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2700 := block2700 ++ suffix2712
private theorem valid2700 : bitCheck suffix2700 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2700 suffix2712 _ (0x3ff8 <<< 1556) _ check2700 valid2712
private theorem check2688 : bitCheck block2688 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2688 := block2688 ++ suffix2700
private theorem valid2688 : bitCheck suffix2688 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2688 suffix2700 _ (0x3ff8 <<< 1556) _ check2688 valid2700
private theorem check2660 : bitCheck block2660 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2660 := block2660 ++ suffix2688
private theorem valid2660 : bitCheck suffix2660 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2660 suffix2688 _ (0x3ff8 <<< 1556) _ check2660 valid2688
private theorem check2620 : bitCheck block2620 (0x3ff8 <<< 1556) = some 0 := by decide +kernel
private def suffix2620 := block2620 ++ suffix2660
private theorem valid2620 : bitCheck suffix2620 (0x78 <<< 1556) = some 0 := bit_join block2620 suffix2660 _ (0x3ff8 <<< 1556) _ check2620 valid2660
private theorem check2616 : bitCheck block2616 0 = some 0 := by decide +kernel
private def suffix2616 := block2616 ++ suffix2620
private theorem valid2616 : bitCheck suffix2616 (0x78 <<< 1556) = some 0 := bit_join block2616 suffix2620 _ 0 _ check2616 valid2620
private theorem check2592 : bitCheck block2592 0 = some 0 := by decide +kernel
private def suffix2592 := block2592 ++ suffix2616
private theorem valid2592 : bitCheck suffix2592 (0x78 <<< 1556) = some 0 := bit_join block2592 suffix2616 _ 0 _ check2592 valid2616
private theorem check2580 : bitCheck block2580 0 = some 0 := by decide +kernel
private def suffix2580 := block2580 ++ suffix2592
private theorem valid2580 : bitCheck suffix2580 (0x78 <<< 1556) = some 0 := bit_join block2580 suffix2592 _ 0 _ check2580 valid2592
private theorem check2540 : bitCheck block2540 0 = some 0 := by decide +kernel
private def suffix2540 := block2540 ++ suffix2580
private theorem valid2540 : bitCheck suffix2540 (0x78 <<< 1556) = some 0 := bit_join block2540 suffix2580 _ 0 _ check2540 valid2580
private theorem check2520 : bitCheck block2520 0 = some (0x1ff0000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2520 := block2520 ++ suffix2540
private theorem valid2520 : bitCheck suffix2520 (0x78 <<< 1556) = some (0x1ff0000000000000000000000000000 <<< 1556) := bit_join block2520 suffix2540 _ 0 _ check2520 valid2540
private theorem check2500 : bitCheck block2500 (0x1ff0000000000000000000000000000 <<< 1556) = some (0x1fffffff00000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2500 := block2500 ++ suffix2520
private theorem valid2500 : bitCheck suffix2500 (0x78 <<< 1556) = some (0x1fffffff00000000000000000000000 <<< 1556) := bit_join block2500 suffix2520 _ (0x1ff0000000000000000000000000000 <<< 1556) _ check2500 valid2520
private theorem check2496 : bitCheck block2496 (0x1fffffff00000000000000000000000 <<< 1556) = some (0x1ffffffff0000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2496 := block2496 ++ suffix2500
private theorem valid2496 : bitCheck suffix2496 (0x78 <<< 1556) = some (0x1ffffffff0000000000000000000000 <<< 1556) := bit_join block2496 suffix2500 _ (0x1fffffff00000000000000000000000 <<< 1556) _ check2496 valid2500
private theorem check2460 : bitCheck block2460 (0x1ffffffff0000000000000000000000 <<< 1556) = some (0x1fffffffffffffffe0003e000000000 <<< 1556) := by decide +kernel
private def suffix2460 := block2460 ++ suffix2496
private theorem valid2460 : bitCheck suffix2460 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003e000000000 <<< 1556) := bit_join block2460 suffix2496 _ (0x1ffffffff0000000000000000000000 <<< 1556) _ check2460 valid2496
private theorem check2424 : bitCheck block2424 (0x1fffffffffffffffe0003e000000000 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2424 := block2424 ++ suffix2460
private theorem valid2424 : bitCheck suffix2424 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2424 suffix2460 _ (0x1fffffffffffffffe0003e000000000 <<< 1556) _ check2424 valid2460
private theorem check2420 : bitCheck block2420 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2420 := block2420 ++ suffix2424
private theorem valid2420 : bitCheck suffix2420 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2420 suffix2424 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2420 valid2424
private theorem check2400 : bitCheck block2400 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2400 := block2400 ++ suffix2420
private theorem valid2400 : bitCheck suffix2400 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2400 suffix2420 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2400 valid2420
private theorem check2380 : bitCheck block2380 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2380 := block2380 ++ suffix2400
private theorem valid2380 : bitCheck suffix2380 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2380 suffix2400 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2380 valid2400
private theorem check2340 : bitCheck block2340 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2340 := block2340 ++ suffix2380
private theorem valid2340 : bitCheck suffix2340 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2340 suffix2380 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2340 valid2380
private theorem check2328 : bitCheck block2328 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2328 := block2328 ++ suffix2340
private theorem valid2328 : bitCheck suffix2328 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2328 suffix2340 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2328 valid2340
private theorem check2304 : bitCheck block2304 (0x1fffffffffffffffe0003fffffffff8 <<< 1556) = some (0x1fffffffffffffffe0003ffffffffe0 <<< 1556) := by decide +kernel
private def suffix2304 := block2304 ++ suffix2328
private theorem valid2304 : bitCheck suffix2304 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003ffffffffe0 <<< 1556) := bit_join block2304 suffix2328 _ (0x1fffffffffffffffe0003fffffffff8 <<< 1556) _ check2304 valid2328
private theorem check2300 : bitCheck block2300 (0x1fffffffffffffffe0003ffffffffe0 <<< 1556) = some (0x1fffffffffffffffe0003ffffffff80 <<< 1556) := by decide +kernel
private def suffix2300 := block2300 ++ suffix2304
private theorem valid2300 : bitCheck suffix2300 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003ffffffff80 <<< 1556) := bit_join block2300 suffix2304 _ (0x1fffffffffffffffe0003ffffffffe0 <<< 1556) _ check2300 valid2304
private theorem check2260 : bitCheck block2260 (0x1fffffffffffffffe0003ffffffff80 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2260 := block2260 ++ suffix2300
private theorem valid2260 : bitCheck suffix2260 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2260 suffix2300 _ (0x1fffffffffffffffe0003ffffffff80 <<< 1556) _ check2260 valid2300
private def group1 := suffix2260
private theorem cert1 : bitCheck group1 (0x78 <<< 1556) = some (0x1fffffffffffffffe0003fffffffff8 <<< 1556) := valid2260
private def block0 : List Gate := [
  .cx 418 1723,
  .cx 948 1723,
  .cx 400 930,
  .ccx 255 930 400,
  .cx 400 930,
  .cx 401 931,
  .ccx 255 931 401,
  .cx 401 931,
  .cx 402 932,
  .ccx 255 932 402,
  .cx 402 932,
  .cx 403 933,
  .ccx 255 933 403,
  .cx 403 933,
  .cx 404 934,
  .ccx 255 934 404,
  .cx 404 934,
  .cx 405 935,
  .ccx 255 935 405,
  .cx 405 935,
  .cx 406 936,
  .ccx 255 936 406,
  .cx 406 936,
  .cx 407 937]
private def block24 : List Gate := [
  .ccx 255 937 407,
  .cx 407 937,
  .cx 408 938,
  .ccx 255 938 408,
  .cx 408 938,
  .cx 409 939,
  .ccx 255 939 409,
  .cx 409 939,
  .cx 410 940,
  .ccx 255 940 410,
  .cx 410 940,
  .cx 411 941,
  .ccx 255 941 411,
  .cx 411 941,
  .cx 412 942,
  .ccx 255 942 412]
private def block40 : List Gate := [
  .cx 412 942,
  .cx 413 943,
  .ccx 255 943 413,
  .cx 413 943,
  .cx 414 944,
  .ccx 255 944 414,
  .cx 414 944,
  .cx 415 945,
  .ccx 255 945 415,
  .cx 415 945,
  .cx 416 946,
  .ccx 255 946 416,
  .cx 416 946,
  .cx 417 947,
  .ccx 255 947 417,
  .cx 417 947,
  .cx 418 948,
  .ccx 255 948 418,
  .cx 418 948,
  .cx 1723 930,
  .cx 1723 931,
  .cx 1723 932,
  .cx 1723 933,
  .cx 1723 934,
  .cx 1723 935,
  .cx 1723 936,
  .cx 1723 937,
  .cx 1723 938,
  .cx 1723 939,
  .cx 1723 940,
  .cx 1723 941,
  .cx 1723 942,
  .cx 1723 943,
  .cx 1723 944,
  .cx 1723 945,
  .cx 1723 946,
  .cx 1723 947,
  .cx 1723 948,
  .x 241,
  .x 242]
private def block80 : List Gate := [
  .x 243,
  .x 244,
  .x 245,
  .x 246,
  .x 247,
  .x 248,
  .x 249,
  .x 250,
  .x 251,
  .x 252,
  .x 253,
  .x 254,
  .x 255,
  .x 930,
  .x 931,
  .x 932]
private def block96 : List Gate := [
  .x 933,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .x 941,
  .x 942,
  .x 943,
  .x 944,
  .x 945,
  .x 946,
  .x 947,
  .x 948,
  .make 930 931 1557,
  .make 1557 932 1558,
  .make 1558 933 1559,
  .make 1559 934 1560,
  .make 1560 935 1561,
  .make 1561 936 1562,
  .make 1562 937 1563,
  .make 1563 938 1564]
private def block120 : List Gate := [
  .make 1564 939 1565,
  .make 1565 940 1566,
  .make 1566 941 1567,
  .make 1567 942 1568,
  .make 1568 943 1569,
  .make 1569 944 1570,
  .make 1570 945 1571,
  .make 1571 946 1572,
  .make 1572 947 1573,
  .make 1573 948 1574,
  .cx 1574 1556,
  .x 1556,
  .pop 1573 948 1574,
  .pop 1572 947 1573,
  .pop 1571 946 1572,
  .pop 1570 945 1571,
  .pop 1569 944 1570,
  .pop 1568 943 1569,
  .pop 1567 942 1568,
  .pop 1566 941 1567,
  .pop 1565 940 1566,
  .pop 1564 939 1565,
  .pop 1563 938 1564,
  .pop 1562 937 1563,
  .pop 1561 936 1562,
  .pop 1560 935 1561,
  .pop 1559 934 1560,
  .pop 1558 933 1559,
  .pop 1557 932 1558,
  .pop 930 931 1557,
  .x 948,
  .x 947,
  .x 946,
  .x 945,
  .x 944,
  .x 943,
  .x 942,
  .x 941,
  .x 940,
  .x 939]
private def block160 : List Gate := [
  .x 938,
  .x 937,
  .x 936,
  .x 935,
  .x 934,
  .x 933,
  .x 932,
  .x 931,
  .x 930,
  .x 1557,
  .cx 400 1557,
  .make 930 1557 1558,
  .make 931 1558 1559,
  .make 932 1559 1560,
  .make 933 1560 1561,
  .make 934 1561 1562,
  .make 935 1562 1563,
  .make 936 1563 1564,
  .make 937 1564 1565,
  .make 938 1565 1566,
  .make 939 1566 1567,
  .make 940 1567 1568,
  .make 941 1568 1569,
  .make 942 1569 1570,
  .make 943 1570 1571,
  .make 944 1571 1572,
  .make 945 1572 1573,
  .make 946 1573 1574,
  .make 947 1574 1575,
  .cx 1575 948,
  .pop 947 1574 1575,
  .cx 1574 947]
private def block192 : List Gate := [
  .pop 946 1573 1574,
  .cx 1573 946,
  .pop 945 1572 1573,
  .cx 1572 945,
  .pop 944 1571 1572,
  .cx 1571 944,
  .pop 943 1570 1571,
  .cx 1570 943]
private def block200 : List Gate := [
  .pop 942 1569 1570,
  .cx 1569 942,
  .pop 941 1568 1569,
  .cx 1568 941,
  .pop 940 1567 1568,
  .cx 1567 940,
  .pop 939 1566 1567,
  .cx 1566 939,
  .pop 938 1565 1566,
  .cx 1565 938,
  .pop 937 1564 1565,
  .cx 1564 937,
  .pop 936 1563 1564,
  .cx 1563 936,
  .pop 935 1562 1563,
  .cx 1562 935]
private def block216 : List Gate := [
  .pop 934 1561 1562,
  .cx 1561 934,
  .pop 933 1560 1561,
  .cx 1560 933,
  .pop 932 1559 1560,
  .cx 1559 932,
  .pop 931 1558 1559,
  .cx 1558 931,
  .ccx 1556 401 931,
  .ccx 1556 402 932,
  .ccx 1556 403 933,
  .ccx 1556 404 934,
  .ccx 1556 405 935,
  .ccx 1556 406 936,
  .ccx 1556 407 937,
  .ccx 1556 408 938,
  .ccx 1556 409 939,
  .ccx 1556 410 940,
  .ccx 1556 411 941,
  .ccx 1556 412 942,
  .ccx 1556 413 943,
  .ccx 1556 414 944,
  .ccx 1556 415 945,
  .ccx 1556 416 946]
private def block240 : List Gate := [
  .ccx 1556 417 947,
  .ccx 1556 418 948,
  .make 1721 1722 1559,
  .cx 1721 1560,
  .cx 1559 1560,
  .make 1560 1269 1561,
  .cx 1561 1560,
  .make 1560 1270 1562,
  .cx 1562 1560,
  .make 1560 1271 1563,
  .cx 1563 1560,
  .make 1560 1272 1564,
  .cx 1564 1560,
  .make 1560 1273 1565,
  .cx 1565 1560,
  .make 1560 1274 1566,
  .cx 1566 1560,
  .make 1560 1275 1567,
  .cx 1567 1560,
  .make 1560 1276 1568,
  .cx 1568 1560,
  .make 1560 1277 1569,
  .cx 1569 1560,
  .make 1560 1278 1570,
  .cx 1570 1560,
  .make 1560 1279 1571,
  .cx 1571 1560,
  .make 1560 1280 1572,
  .cx 1572 1560,
  .make 1560 1281 1573,
  .cx 1573 1560,
  .make 1560 1282 1574,
  .cx 1574 1560,
  .make 1560 1283 1575,
  .cx 1575 1560,
  .cx 1559 1725,
  .cx 1561 1725,
  .cx 1562 1725,
  .cx 1563 1725,
  .cx 1564 1725]
private def block280 : List Gate := [
  .cx 1565 1725,
  .cx 1559 1576,
  .cx 1561 1576,
  .make 254 255 1577,
  .make 253 1577 1578,
  .make 252 1578 1579,
  .make 251 1579 1580,
  .make 250 1580 1581]
private def block288 : List Gate := [
  .make 249 1581 1582,
  .make 248 1582 1583,
  .make 247 1583 1584,
  .make 246 1584 1585,
  .make 245 1585 1586,
  .make 244 1586 1587,
  .make 243 1587 1588,
  .make 1562 1588 1589,
  .make 1563 1586 1590,
  .make 1564 1584 1591,
  .make 1565 1582 1592,
  .make 1566 1580 1593,
  .make 1567 1578 1594,
  .make 1568 255 1595,
  .ccx 1576 401 1724,
  .ccx 1562 402 1724,
  .ccx 1563 403 1724,
  .ccx 1564 404 1724,
  .ccx 1565 405 1724,
  .ccx 1566 406 1724,
  .ccx 1567 407 1724,
  .ccx 1568 408 1724,
  .ccx 1569 409 1724,
  .ccx 1570 410 1724]
private def block312 : List Gate := [
  .ccx 1571 411 1724,
  .ccx 1572 412 1724,
  .ccx 1573 413 1724,
  .ccx 1574 414 1724,
  .ccx 1575 415 1724,
  .ccx 1560 416 1724,
  .cx 1589 1596,
  .cx 1590 1596]
private def block320 : List Gate := [
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .make 1724 1596 1597,
  .cx 1597 1718,
  .cx 1597 1719,
  .cx 1597 1720,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971]
private def block360 : List Gate := [
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995]
private def block384 : List Gate := [
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011]
private def block400 : List Gate := [
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019]
private def block408 : List Gate := [
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030,
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034,
  .cx 1597 1035,
  .cx 1597 1036,
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .make 1718 1724 1598,
  .make 1719 1598 1599,
  .make 1720 1599 1600,
  .make 949 1600 1601,
  .make 950 1601 1602,
  .make 951 1602 1603,
  .make 952 1603 1604,
  .make 953 1604 1605,
  .make 954 1605 1606]
private def block440 : List Gate := [
  .make 955 1606 1607,
  .make 956 1607 1608,
  .make 957 1608 1609,
  .make 958 1609 1610,
  .make 959 1610 1611,
  .make 960 1611 1612,
  .make 961 1612 1613,
  .make 962 1613 1614,
  .make 963 1614 1615,
  .make 964 1615 1616,
  .make 965 1616 1617,
  .make 966 1617 1618,
  .make 967 1618 1619,
  .make 968 1619 1620,
  .make 969 1620 1621,
  .make 970 1621 1622,
  .make 971 1622 1623,
  .make 972 1623 1624,
  .make 973 1624 1625,
  .make 974 1625 1626,
  .make 975 1626 1627,
  .make 976 1627 1628,
  .make 977 1628 1629,
  .make 978 1629 1630,
  .make 979 1630 1631,
  .make 980 1631 1632,
  .make 981 1632 1633,
  .make 982 1633 1634,
  .make 983 1634 1635,
  .make 984 1635 1636,
  .make 985 1636 1637,
  .make 986 1637 1638,
  .make 987 1638 1639,
  .make 988 1639 1640,
  .make 989 1640 1641,
  .make 990 1641 1642,
  .make 991 1642 1643,
  .make 992 1643 1644,
  .make 993 1644 1645,
  .make 994 1645 1646]
private def block480 : List Gate := [
  .make 995 1646 1647,
  .make 996 1647 1648,
  .make 997 1648 1649,
  .make 998 1649 1650,
  .make 999 1650 1651,
  .make 1000 1651 1652,
  .make 1001 1652 1653,
  .make 1002 1653 1654,
  .make 1003 1654 1655,
  .make 1004 1655 1656,
  .make 1005 1656 1657,
  .make 1006 1657 1658,
  .make 1007 1658 1659,
  .make 1008 1659 1660,
  .make 1009 1660 1661,
  .make 1010 1661 1662,
  .make 1011 1662 1663,
  .make 1012 1663 1664,
  .make 1013 1664 1665,
  .make 1014 1665 1666,
  .make 1015 1666 1667,
  .make 1016 1667 1668,
  .make 1017 1668 1669,
  .make 1018 1669 1670]
private def block504 : List Gate := [
  .make 1019 1670 1671,
  .make 1020 1671 1672,
  .make 1021 1672 1673,
  .make 1022 1673 1674,
  .make 1023 1674 1675,
  .make 1024 1675 1676,
  .make 1025 1676 1677,
  .make 1026 1677 1678,
  .make 1027 1678 1679,
  .make 1028 1679 1680,
  .make 1029 1680 1681,
  .make 1030 1681 1682,
  .make 1031 1682 1683,
  .make 1032 1683 1684,
  .make 1033 1684 1685,
  .make 1034 1685 1686]
private def block520 : List Gate := [
  .make 1035 1686 1687,
  .make 1036 1687 1688,
  .make 1037 1688 1689,
  .make 1038 1689 1690,
  .make 1039 1690 1691,
  .make 1040 1691 1692,
  .make 1041 1692 1693,
  .cx 1693 1042,
  .pop 1041 1692 1693,
  .cx 1692 1041,
  .pop 1040 1691 1692,
  .cx 1691 1040,
  .pop 1039 1690 1691,
  .cx 1690 1039,
  .pop 1038 1689 1690,
  .cx 1689 1038,
  .pop 1037 1688 1689,
  .cx 1688 1037,
  .pop 1036 1687 1688,
  .cx 1687 1036,
  .pop 1035 1686 1687,
  .cx 1686 1035,
  .pop 1034 1685 1686,
  .cx 1685 1034,
  .pop 1033 1684 1685,
  .cx 1684 1033,
  .pop 1032 1683 1684,
  .cx 1683 1032,
  .pop 1031 1682 1683,
  .cx 1682 1031,
  .pop 1030 1681 1682,
  .cx 1681 1030,
  .pop 1029 1680 1681,
  .cx 1680 1029,
  .pop 1028 1679 1680,
  .cx 1679 1028,
  .pop 1027 1678 1679,
  .cx 1678 1027,
  .pop 1026 1677 1678,
  .cx 1677 1026]
private def block560 : List Gate := [
  .pop 1025 1676 1677,
  .cx 1676 1025,
  .pop 1024 1675 1676,
  .cx 1675 1024,
  .pop 1023 1674 1675,
  .cx 1674 1023,
  .pop 1022 1673 1674,
  .cx 1673 1022,
  .pop 1021 1672 1673,
  .cx 1672 1021,
  .pop 1020 1671 1672,
  .cx 1671 1020,
  .pop 1019 1670 1671,
  .cx 1670 1019,
  .pop 1018 1669 1670,
  .cx 1669 1018]
private def block576 : List Gate := [
  .pop 1017 1668 1669,
  .cx 1668 1017,
  .pop 1016 1667 1668,
  .cx 1667 1016,
  .pop 1015 1666 1667,
  .cx 1666 1015,
  .pop 1014 1665 1666,
  .cx 1665 1014,
  .pop 1013 1664 1665,
  .cx 1664 1013,
  .pop 1012 1663 1664,
  .cx 1663 1012,
  .pop 1011 1662 1663,
  .cx 1662 1011,
  .pop 1010 1661 1662,
  .cx 1661 1010,
  .pop 1009 1660 1661,
  .cx 1660 1009,
  .pop 1008 1659 1660,
  .cx 1659 1008,
  .pop 1007 1658 1659,
  .cx 1658 1007,
  .pop 1006 1657 1658,
  .cx 1657 1006]
private def block600 : List Gate := [
  .pop 1005 1656 1657,
  .cx 1656 1005,
  .pop 1004 1655 1656,
  .cx 1655 1004,
  .pop 1003 1654 1655,
  .cx 1654 1003,
  .pop 1002 1653 1654,
  .cx 1653 1002,
  .pop 1001 1652 1653,
  .cx 1652 1001,
  .pop 1000 1651 1652,
  .cx 1651 1000,
  .pop 999 1650 1651,
  .cx 1650 999,
  .pop 998 1649 1650,
  .cx 1649 998,
  .pop 997 1648 1649,
  .cx 1648 997,
  .pop 996 1647 1648,
  .cx 1647 996,
  .pop 995 1646 1647,
  .cx 1646 995,
  .pop 994 1645 1646,
  .cx 1645 994,
  .pop 993 1644 1645,
  .cx 1644 993,
  .pop 992 1643 1644,
  .cx 1643 992,
  .pop 991 1642 1643,
  .cx 1642 991,
  .pop 990 1641 1642,
  .cx 1641 990,
  .pop 989 1640 1641,
  .cx 1640 989,
  .pop 988 1639 1640,
  .cx 1639 988,
  .pop 987 1638 1639,
  .cx 1638 987,
  .pop 986 1637 1638,
  .cx 1637 986]
private def block640 : List Gate := [
  .pop 985 1636 1637,
  .cx 1636 985,
  .pop 984 1635 1636,
  .cx 1635 984,
  .pop 983 1634 1635,
  .cx 1634 983,
  .pop 982 1633 1634,
  .cx 1633 982,
  .pop 981 1632 1633,
  .cx 1632 981,
  .pop 980 1631 1632,
  .cx 1631 980,
  .pop 979 1630 1631,
  .cx 1630 979,
  .pop 978 1629 1630,
  .cx 1629 978,
  .pop 977 1628 1629,
  .cx 1628 977,
  .pop 976 1627 1628,
  .cx 1627 976,
  .pop 975 1626 1627,
  .cx 1626 975,
  .pop 974 1625 1626,
  .cx 1625 974,
  .pop 973 1624 1625,
  .cx 1624 973,
  .pop 972 1623 1624,
  .cx 1623 972,
  .pop 971 1622 1623,
  .cx 1622 971,
  .pop 970 1621 1622,
  .cx 1621 970]
private def block672 : List Gate := [
  .pop 969 1620 1621,
  .cx 1620 969,
  .pop 968 1619 1620,
  .cx 1619 968,
  .pop 967 1618 1619,
  .cx 1618 967,
  .pop 966 1617 1618,
  .cx 1617 966]
private def block680 : List Gate := [
  .pop 965 1616 1617,
  .cx 1616 965,
  .pop 964 1615 1616,
  .cx 1615 964,
  .pop 963 1614 1615,
  .cx 1614 963,
  .pop 962 1613 1614,
  .cx 1613 962,
  .pop 961 1612 1613,
  .cx 1612 961,
  .pop 960 1611 1612,
  .cx 1611 960,
  .pop 959 1610 1611,
  .cx 1610 959,
  .pop 958 1609 1610,
  .cx 1609 958]
private def block696 : List Gate := [
  .pop 957 1608 1609,
  .cx 1608 957,
  .pop 956 1607 1608,
  .cx 1607 956,
  .pop 955 1606 1607,
  .cx 1606 955,
  .pop 954 1605 1606,
  .cx 1605 954,
  .pop 953 1604 1605,
  .cx 1604 953,
  .pop 952 1603 1604,
  .cx 1603 952,
  .pop 951 1602 1603,
  .cx 1602 951,
  .pop 950 1601 1602,
  .cx 1601 950,
  .pop 949 1600 1601,
  .cx 1600 949,
  .pop 1720 1599 1600,
  .cx 1599 1720,
  .pop 1719 1598 1599,
  .cx 1598 1719,
  .pop 1718 1724 1598,
  .cx 1724 1718]
private def block720 : List Gate := [
  .cx 1597 1718,
  .cx 1597 1719,
  .cx 1597 1720,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985]
private def block760 : List Gate := [
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993]
private def block768 : List Gate := [
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017]
private def block792 : List Gate := [
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025]
private def block800 : List Gate := [
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030,
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034,
  .cx 1597 1035,
  .cx 1597 1036,
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1042 1598,
  .ccx 1613 1598 1042,
  .cx 1042 1598,
  .cx 1041 1042,
  .ccx 1613 1042 1041,
  .cx 1041 1042,
  .cx 1040 1041,
  .ccx 1613 1041 1040,
  .cx 1040 1041,
  .cx 1039 1040,
  .ccx 1613 1040 1039,
  .cx 1039 1040,
  .cx 1038 1039,
  .ccx 1613 1039 1038,
  .cx 1038 1039]
private def block840 : List Gate := [
  .cx 1037 1038,
  .ccx 1613 1038 1037,
  .cx 1037 1038,
  .cx 1036 1037,
  .ccx 1613 1037 1036,
  .cx 1036 1037,
  .cx 1035 1036,
  .ccx 1613 1036 1035,
  .cx 1035 1036,
  .cx 1034 1035,
  .ccx 1613 1035 1034,
  .cx 1034 1035,
  .cx 1033 1034,
  .ccx 1613 1034 1033,
  .cx 1033 1034,
  .cx 1032 1033,
  .ccx 1613 1033 1032,
  .cx 1032 1033,
  .cx 1031 1032,
  .ccx 1613 1032 1031,
  .cx 1031 1032,
  .cx 1030 1031,
  .ccx 1613 1031 1030,
  .cx 1030 1031]
private def block864 : List Gate := [
  .cx 1029 1030,
  .ccx 1613 1030 1029,
  .cx 1029 1030,
  .cx 1028 1029,
  .ccx 1613 1029 1028,
  .cx 1028 1029,
  .cx 1027 1028,
  .ccx 1613 1028 1027,
  .cx 1027 1028,
  .cx 1026 1027,
  .ccx 1613 1027 1026,
  .cx 1026 1027,
  .cx 1025 1026,
  .ccx 1613 1026 1025,
  .cx 1025 1026,
  .cx 1024 1025]
private def block880 : List Gate := [
  .ccx 1613 1025 1024,
  .cx 1024 1025,
  .cx 1023 1024,
  .ccx 1613 1024 1023,
  .cx 1023 1024,
  .cx 1022 1023,
  .ccx 1613 1023 1022,
  .cx 1022 1023]
private def block888 : List Gate := [
  .cx 1021 1022,
  .ccx 1613 1022 1021,
  .cx 1021 1022,
  .cx 1020 1021,
  .ccx 1613 1021 1020,
  .cx 1020 1021,
  .cx 1019 1020,
  .ccx 1613 1020 1019,
  .cx 1019 1020,
  .cx 1018 1019,
  .ccx 1613 1019 1018,
  .cx 1018 1019,
  .cx 1017 1018,
  .ccx 1613 1018 1017,
  .cx 1017 1018,
  .cx 1016 1017,
  .ccx 1613 1017 1016,
  .cx 1016 1017,
  .cx 1015 1016,
  .ccx 1613 1016 1015,
  .cx 1015 1016,
  .cx 1014 1015,
  .ccx 1613 1015 1014,
  .cx 1014 1015,
  .cx 1013 1014,
  .ccx 1613 1014 1013,
  .cx 1013 1014,
  .cx 1012 1013,
  .ccx 1613 1013 1012,
  .cx 1012 1013,
  .cx 1011 1012,
  .ccx 1613 1012 1011]
private def block920 : List Gate := [
  .cx 1011 1012,
  .cx 1010 1011,
  .ccx 1613 1011 1010,
  .cx 1010 1011,
  .cx 1009 1010,
  .ccx 1613 1010 1009,
  .cx 1009 1010,
  .cx 1008 1009,
  .ccx 1613 1009 1008,
  .cx 1008 1009,
  .cx 1007 1008,
  .ccx 1613 1008 1007,
  .cx 1007 1008,
  .cx 1006 1007,
  .ccx 1613 1007 1006,
  .cx 1006 1007,
  .cx 1005 1006,
  .ccx 1613 1006 1005,
  .cx 1005 1006,
  .cx 1004 1005,
  .ccx 1613 1005 1004,
  .cx 1004 1005,
  .cx 1003 1004,
  .ccx 1613 1004 1003,
  .cx 1003 1004,
  .cx 1002 1003,
  .ccx 1613 1003 1002,
  .cx 1002 1003,
  .cx 1001 1002,
  .ccx 1613 1002 1001,
  .cx 1001 1002,
  .cx 1000 1001,
  .ccx 1613 1001 1000,
  .cx 1000 1001,
  .cx 999 1000,
  .ccx 1613 1000 999,
  .cx 999 1000,
  .cx 998 999,
  .ccx 1613 999 998,
  .cx 998 999]
private def block960 : List Gate := [
  .cx 997 998,
  .ccx 1613 998 997,
  .cx 997 998,
  .cx 996 997,
  .ccx 1613 997 996,
  .cx 996 997,
  .cx 995 996,
  .ccx 1613 996 995,
  .cx 995 996,
  .cx 994 995,
  .ccx 1613 995 994,
  .cx 994 995,
  .cx 993 994,
  .ccx 1613 994 993,
  .cx 993 994,
  .cx 992 993,
  .ccx 1613 993 992,
  .cx 992 993,
  .cx 991 992,
  .ccx 1613 992 991,
  .cx 991 992,
  .cx 990 991,
  .ccx 1613 991 990,
  .cx 990 991]
private def block984 : List Gate := [
  .cx 989 990,
  .ccx 1613 990 989,
  .cx 989 990,
  .cx 988 989,
  .ccx 1613 989 988,
  .cx 988 989,
  .cx 987 988,
  .ccx 1613 988 987,
  .cx 987 988,
  .cx 986 987,
  .ccx 1613 987 986,
  .cx 986 987,
  .cx 985 986,
  .ccx 1613 986 985,
  .cx 985 986,
  .cx 984 985]
private def block1000 : List Gate := [
  .ccx 1613 985 984,
  .cx 984 985,
  .cx 983 984,
  .ccx 1613 984 983,
  .cx 983 984,
  .cx 982 983,
  .ccx 1613 983 982,
  .cx 982 983,
  .cx 981 982,
  .ccx 1613 982 981,
  .cx 981 982,
  .cx 980 981,
  .ccx 1613 981 980,
  .cx 980 981,
  .cx 979 980,
  .ccx 1613 980 979,
  .cx 979 980,
  .cx 978 979,
  .ccx 1613 979 978,
  .cx 978 979,
  .cx 977 978,
  .ccx 1613 978 977,
  .cx 977 978,
  .cx 976 977,
  .ccx 1613 977 976,
  .cx 976 977,
  .cx 975 976,
  .ccx 1613 976 975,
  .cx 975 976,
  .cx 974 975,
  .ccx 1613 975 974,
  .cx 974 975,
  .cx 973 974,
  .ccx 1613 974 973,
  .cx 973 974,
  .cx 972 973,
  .ccx 1613 973 972,
  .cx 972 973,
  .cx 971 972,
  .ccx 1613 972 971]
private def block1040 : List Gate := [
  .cx 971 972,
  .cx 970 971,
  .ccx 1613 971 970,
  .cx 970 971,
  .cx 969 970,
  .ccx 1613 970 969,
  .cx 969 970,
  .cx 968 969,
  .ccx 1613 969 968,
  .cx 968 969,
  .cx 967 968,
  .ccx 1613 968 967,
  .cx 967 968,
  .cx 966 967,
  .ccx 1613 967 966,
  .cx 966 967]
private def block1056 : List Gate := [
  .cx 965 966,
  .ccx 1613 966 965,
  .cx 965 966,
  .cx 964 965,
  .ccx 1613 965 964,
  .cx 964 965,
  .cx 963 964,
  .ccx 1613 964 963,
  .cx 963 964,
  .cx 962 963,
  .ccx 1613 963 962,
  .cx 962 963,
  .cx 961 962,
  .ccx 1613 962 961,
  .cx 961 962,
  .cx 960 961,
  .ccx 1613 961 960,
  .cx 960 961,
  .cx 959 960,
  .ccx 1613 960 959,
  .cx 959 960,
  .cx 958 959,
  .ccx 1613 959 958,
  .cx 958 959]
private def block1080 : List Gate := [
  .cx 957 958,
  .ccx 1613 958 957,
  .cx 957 958,
  .cx 956 957,
  .ccx 1613 957 956,
  .cx 956 957,
  .cx 955 956,
  .ccx 1613 956 955,
  .cx 955 956,
  .cx 954 955,
  .ccx 1613 955 954,
  .cx 954 955,
  .cx 953 954,
  .ccx 1613 954 953,
  .cx 953 954,
  .cx 952 953,
  .ccx 1613 953 952,
  .cx 952 953,
  .cx 951 952,
  .ccx 1613 952 951,
  .cx 951 952,
  .cx 950 951,
  .ccx 1613 951 950,
  .cx 950 951,
  .cx 949 950,
  .ccx 1613 950 949,
  .cx 949 950,
  .cx 1720 949,
  .ccx 1613 949 1720,
  .cx 1720 949,
  .cx 1719 1720,
  .ccx 1613 1720 1719,
  .cx 1719 1720,
  .cx 1718 1719,
  .ccx 1613 1719 1718,
  .cx 1718 1719,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613]
private def block1120 : List Gate := [
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1598 1600,
  .ccx 1613 1600 1598,
  .cx 1598 1600,
  .cx 1042 1599,
  .ccx 1613 1599 1042,
  .cx 1042 1599,
  .cx 1041 1598,
  .ccx 1613 1598 1041,
  .cx 1041 1598,
  .cx 1040 1042,
  .ccx 1613 1042 1040,
  .cx 1040 1042,
  .cx 1039 1041,
  .ccx 1613 1041 1039,
  .cx 1039 1041,
  .cx 1038 1040,
  .ccx 1613 1040 1038,
  .cx 1038 1040,
  .cx 1037 1039,
  .ccx 1613 1039 1037]
private def block1152 : List Gate := [
  .cx 1037 1039,
  .cx 1036 1038,
  .ccx 1613 1038 1036,
  .cx 1036 1038,
  .cx 1035 1037,
  .ccx 1613 1037 1035,
  .cx 1035 1037,
  .cx 1034 1036]
private def block1160 : List Gate := [
  .ccx 1613 1036 1034,
  .cx 1034 1036,
  .cx 1033 1035,
  .ccx 1613 1035 1033,
  .cx 1033 1035,
  .cx 1032 1034,
  .ccx 1613 1034 1032,
  .cx 1032 1034,
  .cx 1031 1033,
  .ccx 1613 1033 1031,
  .cx 1031 1033,
  .cx 1030 1032,
  .ccx 1613 1032 1030,
  .cx 1030 1032,
  .cx 1029 1031,
  .ccx 1613 1031 1029]
private def block1176 : List Gate := [
  .cx 1029 1031,
  .cx 1028 1030,
  .ccx 1613 1030 1028,
  .cx 1028 1030,
  .cx 1027 1029,
  .ccx 1613 1029 1027,
  .cx 1027 1029,
  .cx 1026 1028,
  .ccx 1613 1028 1026,
  .cx 1026 1028,
  .cx 1025 1027,
  .ccx 1613 1027 1025,
  .cx 1025 1027,
  .cx 1024 1026,
  .ccx 1613 1026 1024,
  .cx 1024 1026,
  .cx 1023 1025,
  .ccx 1613 1025 1023,
  .cx 1023 1025,
  .cx 1022 1024,
  .ccx 1613 1024 1022,
  .cx 1022 1024,
  .cx 1021 1023,
  .ccx 1613 1023 1021]
private def block1200 : List Gate := [
  .cx 1021 1023,
  .cx 1020 1022,
  .ccx 1613 1022 1020,
  .cx 1020 1022,
  .cx 1019 1021,
  .ccx 1613 1021 1019,
  .cx 1019 1021,
  .cx 1018 1020,
  .ccx 1613 1020 1018,
  .cx 1018 1020,
  .cx 1017 1019,
  .ccx 1613 1019 1017,
  .cx 1017 1019,
  .cx 1016 1018,
  .ccx 1613 1018 1016,
  .cx 1016 1018,
  .cx 1015 1017,
  .ccx 1613 1017 1015,
  .cx 1015 1017,
  .cx 1014 1016,
  .ccx 1613 1016 1014,
  .cx 1014 1016,
  .cx 1013 1015,
  .ccx 1613 1015 1013,
  .cx 1013 1015,
  .cx 1012 1014,
  .ccx 1613 1014 1012,
  .cx 1012 1014,
  .cx 1011 1013,
  .ccx 1613 1013 1011,
  .cx 1011 1013,
  .cx 1010 1012,
  .ccx 1613 1012 1010,
  .cx 1010 1012,
  .cx 1009 1011,
  .ccx 1613 1011 1009,
  .cx 1009 1011,
  .cx 1008 1010,
  .ccx 1613 1010 1008,
  .cx 1008 1010]
private def block1240 : List Gate := [
  .cx 1007 1009,
  .ccx 1613 1009 1007,
  .cx 1007 1009,
  .cx 1006 1008,
  .ccx 1613 1008 1006,
  .cx 1006 1008,
  .cx 1005 1007,
  .ccx 1613 1007 1005]
private def block1248 : List Gate := [
  .cx 1005 1007,
  .cx 1004 1006,
  .ccx 1613 1006 1004,
  .cx 1004 1006,
  .cx 1003 1005,
  .ccx 1613 1005 1003,
  .cx 1003 1005,
  .cx 1002 1004,
  .ccx 1613 1004 1002,
  .cx 1002 1004,
  .cx 1001 1003,
  .ccx 1613 1003 1001,
  .cx 1001 1003,
  .cx 1000 1002,
  .ccx 1613 1002 1000,
  .cx 1000 1002,
  .cx 999 1001,
  .ccx 1613 1001 999,
  .cx 999 1001,
  .cx 998 1000,
  .ccx 1613 1000 998,
  .cx 998 1000,
  .cx 997 999,
  .ccx 1613 999 997]
private def block1272 : List Gate := [
  .cx 997 999,
  .cx 996 998,
  .ccx 1613 998 996,
  .cx 996 998,
  .cx 995 997,
  .ccx 1613 997 995,
  .cx 995 997,
  .cx 994 996]
private def block1280 : List Gate := [
  .ccx 1613 996 994,
  .cx 994 996,
  .cx 993 995,
  .ccx 1613 995 993,
  .cx 993 995,
  .cx 992 994,
  .ccx 1613 994 992,
  .cx 992 994,
  .cx 991 993,
  .ccx 1613 993 991,
  .cx 991 993,
  .cx 990 992,
  .ccx 1613 992 990,
  .cx 990 992,
  .cx 989 991,
  .ccx 1613 991 989,
  .cx 989 991,
  .cx 988 990,
  .ccx 1613 990 988,
  .cx 988 990,
  .cx 987 989,
  .ccx 1613 989 987,
  .cx 987 989,
  .cx 986 988,
  .ccx 1613 988 986,
  .cx 986 988,
  .cx 985 987,
  .ccx 1613 987 985,
  .cx 985 987,
  .cx 984 986,
  .ccx 1613 986 984,
  .cx 984 986,
  .cx 983 985,
  .ccx 1613 985 983,
  .cx 983 985,
  .cx 982 984,
  .ccx 1613 984 982,
  .cx 982 984,
  .cx 981 983,
  .ccx 1613 983 981]
private def block1320 : List Gate := [
  .cx 981 983,
  .cx 980 982,
  .ccx 1613 982 980,
  .cx 980 982,
  .cx 979 981,
  .ccx 1613 981 979,
  .cx 979 981,
  .cx 978 980,
  .ccx 1613 980 978,
  .cx 978 980,
  .cx 977 979,
  .ccx 1613 979 977,
  .cx 977 979,
  .cx 976 978,
  .ccx 1613 978 976,
  .cx 976 978,
  .cx 975 977,
  .ccx 1613 977 975,
  .cx 975 977,
  .cx 974 976,
  .ccx 1613 976 974,
  .cx 974 976,
  .cx 973 975,
  .ccx 1613 975 973]
private def block1344 : List Gate := [
  .cx 973 975,
  .cx 972 974,
  .ccx 1613 974 972,
  .cx 972 974,
  .cx 971 973,
  .ccx 1613 973 971,
  .cx 971 973,
  .cx 970 972,
  .ccx 1613 972 970,
  .cx 970 972,
  .cx 969 971,
  .ccx 1613 971 969,
  .cx 969 971,
  .cx 968 970,
  .ccx 1613 970 968,
  .cx 968 970]
private def block1360 : List Gate := [
  .cx 967 969,
  .ccx 1613 969 967,
  .cx 967 969,
  .cx 966 968,
  .ccx 1613 968 966,
  .cx 966 968,
  .cx 965 967,
  .ccx 1613 967 965]
private def block1368 : List Gate := [
  .cx 965 967,
  .cx 964 966,
  .ccx 1613 966 964,
  .cx 964 966,
  .cx 963 965,
  .ccx 1613 965 963,
  .cx 963 965,
  .cx 962 964,
  .ccx 1613 964 962,
  .cx 962 964,
  .cx 961 963,
  .ccx 1613 963 961,
  .cx 961 963,
  .cx 960 962,
  .ccx 1613 962 960,
  .cx 960 962,
  .cx 959 961,
  .ccx 1613 961 959,
  .cx 959 961,
  .cx 958 960,
  .ccx 1613 960 958,
  .cx 958 960,
  .cx 957 959,
  .ccx 1613 959 957,
  .cx 957 959,
  .cx 956 958,
  .ccx 1613 958 956,
  .cx 956 958,
  .cx 955 957,
  .ccx 1613 957 955,
  .cx 955 957,
  .cx 954 956]
private def block1400 : List Gate := [
  .ccx 1613 956 954,
  .cx 954 956,
  .cx 953 955,
  .ccx 1613 955 953,
  .cx 953 955,
  .cx 952 954,
  .ccx 1613 954 952,
  .cx 952 954,
  .cx 951 953,
  .ccx 1613 953 951,
  .cx 951 953,
  .cx 950 952,
  .ccx 1613 952 950,
  .cx 950 952,
  .cx 949 951,
  .ccx 1613 951 949,
  .cx 949 951,
  .cx 1720 950,
  .ccx 1613 950 1720,
  .cx 1720 950,
  .cx 1719 949,
  .ccx 1613 949 1719,
  .cx 1719 949,
  .cx 1718 1720,
  .ccx 1613 1720 1718,
  .cx 1718 1720,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613]
private def block1440 : List Gate := [
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1600 1604,
  .ccx 1613 1604 1600,
  .cx 1600 1604,
  .cx 1599 1603,
  .ccx 1613 1603 1599,
  .cx 1599 1603,
  .cx 1598 1602,
  .ccx 1613 1602 1598,
  .cx 1598 1602,
  .cx 1042 1601,
  .ccx 1613 1601 1042,
  .cx 1042 1601,
  .cx 1041 1600,
  .ccx 1613 1600 1041,
  .cx 1041 1600,
  .cx 1040 1599,
  .ccx 1613 1599 1040,
  .cx 1040 1599,
  .cx 1039 1598,
  .ccx 1613 1598 1039,
  .cx 1039 1598,
  .cx 1038 1042]
private def block1464 : List Gate := [
  .ccx 1613 1042 1038,
  .cx 1038 1042,
  .cx 1037 1041,
  .ccx 1613 1041 1037,
  .cx 1037 1041,
  .cx 1036 1040,
  .ccx 1613 1040 1036,
  .cx 1036 1040,
  .cx 1035 1039,
  .ccx 1613 1039 1035,
  .cx 1035 1039,
  .cx 1034 1038,
  .ccx 1613 1038 1034,
  .cx 1034 1038,
  .cx 1033 1037,
  .ccx 1613 1037 1033]
private def block1480 : List Gate := [
  .cx 1033 1037,
  .cx 1032 1036,
  .ccx 1613 1036 1032,
  .cx 1032 1036,
  .cx 1031 1035,
  .ccx 1613 1035 1031,
  .cx 1031 1035,
  .cx 1030 1034,
  .ccx 1613 1034 1030,
  .cx 1030 1034,
  .cx 1029 1033,
  .ccx 1613 1033 1029,
  .cx 1029 1033,
  .cx 1028 1032,
  .ccx 1613 1032 1028,
  .cx 1028 1032,
  .cx 1027 1031,
  .ccx 1613 1031 1027,
  .cx 1027 1031,
  .cx 1026 1030,
  .ccx 1613 1030 1026,
  .cx 1026 1030,
  .cx 1025 1029,
  .ccx 1613 1029 1025,
  .cx 1025 1029,
  .cx 1024 1028,
  .ccx 1613 1028 1024,
  .cx 1024 1028,
  .cx 1023 1027,
  .ccx 1613 1027 1023,
  .cx 1023 1027,
  .cx 1022 1026,
  .ccx 1613 1026 1022,
  .cx 1022 1026,
  .cx 1021 1025,
  .ccx 1613 1025 1021,
  .cx 1021 1025,
  .cx 1020 1024,
  .ccx 1613 1024 1020,
  .cx 1020 1024]
private def block1520 : List Gate := [
  .cx 1019 1023,
  .ccx 1613 1023 1019,
  .cx 1019 1023,
  .cx 1018 1022,
  .ccx 1613 1022 1018,
  .cx 1018 1022,
  .cx 1017 1021,
  .ccx 1613 1021 1017,
  .cx 1017 1021,
  .cx 1016 1020,
  .ccx 1613 1020 1016,
  .cx 1016 1020,
  .cx 1015 1019,
  .ccx 1613 1019 1015,
  .cx 1015 1019,
  .cx 1014 1018]
private def block1536 : List Gate := [
  .ccx 1613 1018 1014,
  .cx 1014 1018,
  .cx 1013 1017,
  .ccx 1613 1017 1013,
  .cx 1013 1017,
  .cx 1012 1016,
  .ccx 1613 1016 1012,
  .cx 1012 1016,
  .cx 1011 1015,
  .ccx 1613 1015 1011,
  .cx 1011 1015,
  .cx 1010 1014,
  .ccx 1613 1014 1010,
  .cx 1010 1014,
  .cx 1009 1013,
  .ccx 1613 1013 1009,
  .cx 1009 1013,
  .cx 1008 1012,
  .ccx 1613 1012 1008,
  .cx 1008 1012,
  .cx 1007 1011,
  .ccx 1613 1011 1007,
  .cx 1007 1011,
  .cx 1006 1010]
private def block1560 : List Gate := [
  .ccx 1613 1010 1006,
  .cx 1006 1010,
  .cx 1005 1009,
  .ccx 1613 1009 1005,
  .cx 1005 1009,
  .cx 1004 1008,
  .ccx 1613 1008 1004,
  .cx 1004 1008,
  .cx 1003 1007,
  .ccx 1613 1007 1003,
  .cx 1003 1007,
  .cx 1002 1006,
  .ccx 1613 1006 1002,
  .cx 1002 1006,
  .cx 1001 1005,
  .ccx 1613 1005 1001,
  .cx 1001 1005,
  .cx 1000 1004,
  .ccx 1613 1004 1000,
  .cx 1000 1004,
  .cx 999 1003,
  .ccx 1613 1003 999,
  .cx 999 1003,
  .cx 998 1002,
  .ccx 1613 1002 998,
  .cx 998 1002,
  .cx 997 1001,
  .ccx 1613 1001 997,
  .cx 997 1001,
  .cx 996 1000,
  .ccx 1613 1000 996,
  .cx 996 1000,
  .cx 995 999,
  .ccx 1613 999 995,
  .cx 995 999,
  .cx 994 998,
  .ccx 1613 998 994,
  .cx 994 998,
  .cx 993 997,
  .ccx 1613 997 993]
private def block1600 : List Gate := [
  .cx 993 997,
  .cx 992 996,
  .ccx 1613 996 992,
  .cx 992 996,
  .cx 991 995,
  .ccx 1613 995 991,
  .cx 991 995,
  .cx 990 994,
  .ccx 1613 994 990,
  .cx 990 994,
  .cx 989 993,
  .ccx 1613 993 989,
  .cx 989 993,
  .cx 988 992,
  .ccx 1613 992 988,
  .cx 988 992,
  .cx 987 991,
  .ccx 1613 991 987,
  .cx 987 991,
  .cx 986 990,
  .ccx 1613 990 986,
  .cx 986 990,
  .cx 985 989,
  .ccx 1613 989 985,
  .cx 985 989,
  .cx 984 988,
  .ccx 1613 988 984,
  .cx 984 988,
  .cx 983 987,
  .ccx 1613 987 983,
  .cx 983 987,
  .cx 982 986]
private def block1632 : List Gate := [
  .ccx 1613 986 982,
  .cx 982 986,
  .cx 981 985,
  .ccx 1613 985 981,
  .cx 981 985,
  .cx 980 984,
  .ccx 1613 984 980,
  .cx 980 984]
private def block1640 : List Gate := [
  .cx 979 983,
  .ccx 1613 983 979,
  .cx 979 983,
  .cx 978 982,
  .ccx 1613 982 978,
  .cx 978 982,
  .cx 977 981,
  .ccx 1613 981 977,
  .cx 977 981,
  .cx 976 980,
  .ccx 1613 980 976,
  .cx 976 980,
  .cx 975 979,
  .ccx 1613 979 975,
  .cx 975 979,
  .cx 974 978]
private def block1656 : List Gate := [
  .ccx 1613 978 974,
  .cx 974 978,
  .cx 973 977,
  .ccx 1613 977 973,
  .cx 973 977,
  .cx 972 976,
  .ccx 1613 976 972,
  .cx 972 976,
  .cx 971 975,
  .ccx 1613 975 971,
  .cx 971 975,
  .cx 970 974,
  .ccx 1613 974 970,
  .cx 970 974,
  .cx 969 973,
  .ccx 1613 973 969,
  .cx 969 973,
  .cx 968 972,
  .ccx 1613 972 968,
  .cx 968 972,
  .cx 967 971,
  .ccx 1613 971 967,
  .cx 967 971,
  .cx 966 970]
private def block1680 : List Gate := [
  .ccx 1613 970 966,
  .cx 966 970,
  .cx 965 969,
  .ccx 1613 969 965,
  .cx 965 969,
  .cx 964 968,
  .ccx 1613 968 964,
  .cx 964 968,
  .cx 963 967,
  .ccx 1613 967 963,
  .cx 963 967,
  .cx 962 966,
  .ccx 1613 966 962,
  .cx 962 966,
  .cx 961 965,
  .ccx 1613 965 961,
  .cx 961 965,
  .cx 960 964,
  .ccx 1613 964 960,
  .cx 960 964,
  .cx 959 963,
  .ccx 1613 963 959,
  .cx 959 963,
  .cx 958 962,
  .ccx 1613 962 958,
  .cx 958 962,
  .cx 957 961,
  .ccx 1613 961 957,
  .cx 957 961,
  .cx 956 960,
  .ccx 1613 960 956,
  .cx 956 960,
  .cx 955 959,
  .ccx 1613 959 955,
  .cx 955 959,
  .cx 954 958,
  .ccx 1613 958 954,
  .cx 954 958,
  .cx 953 957,
  .ccx 1613 957 953]
private def block1720 : List Gate := [
  .cx 953 957,
  .cx 952 956,
  .ccx 1613 956 952,
  .cx 952 956,
  .cx 951 955,
  .ccx 1613 955 951,
  .cx 951 955,
  .cx 950 954]
private def block1728 : List Gate := [
  .ccx 1613 954 950,
  .cx 950 954,
  .cx 949 953,
  .ccx 1613 953 949,
  .cx 949 953,
  .cx 1720 952,
  .ccx 1613 952 1720,
  .cx 1720 952,
  .cx 1719 951,
  .ccx 1613 951 1719,
  .cx 1719 951,
  .cx 1718 950,
  .ccx 1613 950 1718,
  .cx 1718 950,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1569 1613,
  .cx 1570 1613]
private def block1752 : List Gate := [
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1604 1612,
  .ccx 1613 1612 1604]
private def block1760 : List Gate := [
  .cx 1604 1612,
  .cx 1603 1611,
  .ccx 1613 1611 1603,
  .cx 1603 1611,
  .cx 1602 1610,
  .ccx 1613 1610 1602,
  .cx 1602 1610,
  .cx 1601 1609,
  .ccx 1613 1609 1601,
  .cx 1601 1609,
  .cx 1600 1608,
  .ccx 1613 1608 1600,
  .cx 1600 1608,
  .cx 1599 1607,
  .ccx 1613 1607 1599,
  .cx 1599 1607,
  .cx 1598 1606,
  .ccx 1613 1606 1598,
  .cx 1598 1606,
  .cx 1042 1605,
  .ccx 1613 1605 1042,
  .cx 1042 1605,
  .cx 1041 1604,
  .ccx 1613 1604 1041,
  .cx 1041 1604,
  .cx 1040 1603,
  .ccx 1613 1603 1040,
  .cx 1040 1603,
  .cx 1039 1602,
  .ccx 1613 1602 1039,
  .cx 1039 1602,
  .cx 1038 1601,
  .ccx 1613 1601 1038,
  .cx 1038 1601,
  .cx 1037 1600,
  .ccx 1613 1600 1037,
  .cx 1037 1600,
  .cx 1036 1599,
  .ccx 1613 1599 1036,
  .cx 1036 1599]
private def block1800 : List Gate := [
  .cx 1035 1598,
  .ccx 1613 1598 1035,
  .cx 1035 1598,
  .cx 1034 1042,
  .ccx 1613 1042 1034,
  .cx 1034 1042,
  .cx 1033 1041,
  .ccx 1613 1041 1033,
  .cx 1033 1041,
  .cx 1032 1040,
  .ccx 1613 1040 1032,
  .cx 1032 1040,
  .cx 1031 1039,
  .ccx 1613 1039 1031,
  .cx 1031 1039,
  .cx 1030 1038,
  .ccx 1613 1038 1030,
  .cx 1030 1038,
  .cx 1029 1037,
  .ccx 1613 1037 1029,
  .cx 1029 1037,
  .cx 1028 1036,
  .ccx 1613 1036 1028,
  .cx 1028 1036]
private def block1824 : List Gate := [
  .cx 1027 1035,
  .ccx 1613 1035 1027,
  .cx 1027 1035,
  .cx 1026 1034,
  .ccx 1613 1034 1026,
  .cx 1026 1034,
  .cx 1025 1033,
  .ccx 1613 1033 1025,
  .cx 1025 1033,
  .cx 1024 1032,
  .ccx 1613 1032 1024,
  .cx 1024 1032,
  .cx 1023 1031,
  .ccx 1613 1031 1023,
  .cx 1023 1031,
  .cx 1022 1030]
private def block1840 : List Gate := [
  .ccx 1613 1030 1022,
  .cx 1022 1030,
  .cx 1021 1029,
  .ccx 1613 1029 1021,
  .cx 1021 1029,
  .cx 1020 1028,
  .ccx 1613 1028 1020,
  .cx 1020 1028]
private def block1848 : List Gate := [
  .cx 1019 1027,
  .ccx 1613 1027 1019,
  .cx 1019 1027,
  .cx 1018 1026,
  .ccx 1613 1026 1018,
  .cx 1018 1026,
  .cx 1017 1025,
  .ccx 1613 1025 1017,
  .cx 1017 1025,
  .cx 1016 1024,
  .ccx 1613 1024 1016,
  .cx 1016 1024,
  .cx 1015 1023,
  .ccx 1613 1023 1015,
  .cx 1015 1023,
  .cx 1014 1022,
  .ccx 1613 1022 1014,
  .cx 1014 1022,
  .cx 1013 1021,
  .ccx 1613 1021 1013,
  .cx 1013 1021,
  .cx 1012 1020,
  .ccx 1613 1020 1012,
  .cx 1012 1020,
  .cx 1011 1019,
  .ccx 1613 1019 1011,
  .cx 1011 1019,
  .cx 1010 1018,
  .ccx 1613 1018 1010,
  .cx 1010 1018,
  .cx 1009 1017,
  .ccx 1613 1017 1009]
private def block1880 : List Gate := [
  .cx 1009 1017,
  .cx 1008 1016,
  .ccx 1613 1016 1008,
  .cx 1008 1016,
  .cx 1007 1015,
  .ccx 1613 1015 1007,
  .cx 1007 1015,
  .cx 1006 1014,
  .ccx 1613 1014 1006,
  .cx 1006 1014,
  .cx 1005 1013,
  .ccx 1613 1013 1005,
  .cx 1005 1013,
  .cx 1004 1012,
  .ccx 1613 1012 1004,
  .cx 1004 1012,
  .cx 1003 1011,
  .ccx 1613 1011 1003,
  .cx 1003 1011,
  .cx 1002 1010,
  .ccx 1613 1010 1002,
  .cx 1002 1010,
  .cx 1001 1009,
  .ccx 1613 1009 1001,
  .cx 1001 1009,
  .cx 1000 1008,
  .ccx 1613 1008 1000,
  .cx 1000 1008,
  .cx 999 1007,
  .ccx 1613 1007 999,
  .cx 999 1007,
  .cx 998 1006,
  .ccx 1613 1006 998,
  .cx 998 1006,
  .cx 997 1005,
  .ccx 1613 1005 997,
  .cx 997 1005,
  .cx 996 1004,
  .ccx 1613 1004 996,
  .cx 996 1004]
private def block1920 : List Gate := [
  .cx 995 1003,
  .ccx 1613 1003 995,
  .cx 995 1003,
  .cx 994 1002,
  .ccx 1613 1002 994,
  .cx 994 1002,
  .cx 993 1001,
  .ccx 1613 1001 993,
  .cx 993 1001,
  .cx 992 1000,
  .ccx 1613 1000 992,
  .cx 992 1000,
  .cx 991 999,
  .ccx 1613 999 991,
  .cx 991 999,
  .cx 990 998,
  .ccx 1613 998 990,
  .cx 990 998,
  .cx 989 997,
  .ccx 1613 997 989,
  .cx 989 997,
  .cx 988 996,
  .ccx 1613 996 988,
  .cx 988 996]
private def block1944 : List Gate := [
  .cx 987 995,
  .ccx 1613 995 987,
  .cx 987 995,
  .cx 986 994,
  .ccx 1613 994 986,
  .cx 986 994,
  .cx 985 993,
  .ccx 1613 993 985,
  .cx 985 993,
  .cx 984 992,
  .ccx 1613 992 984,
  .cx 984 992,
  .cx 983 991,
  .ccx 1613 991 983,
  .cx 983 991,
  .cx 982 990]
private def block1960 : List Gate := [
  .ccx 1613 990 982,
  .cx 982 990,
  .cx 981 989,
  .ccx 1613 989 981,
  .cx 981 989,
  .cx 980 988,
  .ccx 1613 988 980,
  .cx 980 988,
  .cx 979 987,
  .ccx 1613 987 979,
  .cx 979 987,
  .cx 978 986,
  .ccx 1613 986 978,
  .cx 978 986,
  .cx 977 985,
  .ccx 1613 985 977,
  .cx 977 985,
  .cx 976 984,
  .ccx 1613 984 976,
  .cx 976 984,
  .cx 975 983,
  .ccx 1613 983 975,
  .cx 975 983,
  .cx 974 982,
  .ccx 1613 982 974,
  .cx 974 982,
  .cx 973 981,
  .ccx 1613 981 973,
  .cx 973 981,
  .cx 972 980,
  .ccx 1613 980 972,
  .cx 972 980,
  .cx 971 979,
  .ccx 1613 979 971,
  .cx 971 979,
  .cx 970 978,
  .ccx 1613 978 970,
  .cx 970 978,
  .cx 969 977,
  .ccx 1613 977 969]
private def block2000 : List Gate := [
  .cx 969 977,
  .cx 968 976,
  .ccx 1613 976 968,
  .cx 968 976,
  .cx 967 975,
  .ccx 1613 975 967,
  .cx 967 975,
  .cx 966 974,
  .ccx 1613 974 966,
  .cx 966 974,
  .cx 965 973,
  .ccx 1613 973 965,
  .cx 965 973,
  .cx 964 972,
  .ccx 1613 972 964,
  .cx 964 972]
private def block2016 : List Gate := [
  .cx 963 971,
  .ccx 1613 971 963,
  .cx 963 971,
  .cx 962 970,
  .ccx 1613 970 962,
  .cx 962 970,
  .cx 961 969,
  .ccx 1613 969 961,
  .cx 961 969,
  .cx 960 968,
  .ccx 1613 968 960,
  .cx 960 968,
  .cx 959 967,
  .ccx 1613 967 959,
  .cx 959 967,
  .cx 958 966,
  .ccx 1613 966 958,
  .cx 958 966,
  .cx 957 965,
  .ccx 1613 965 957,
  .cx 957 965,
  .cx 956 964,
  .ccx 1613 964 956,
  .cx 956 964]
private def block2040 : List Gate := [
  .cx 955 963,
  .ccx 1613 963 955,
  .cx 955 963,
  .cx 954 962,
  .ccx 1613 962 954,
  .cx 954 962,
  .cx 953 961,
  .ccx 1613 961 953,
  .cx 953 961,
  .cx 952 960,
  .ccx 1613 960 952,
  .cx 952 960,
  .cx 951 959,
  .ccx 1613 959 951,
  .cx 951 959,
  .cx 950 958,
  .ccx 1613 958 950,
  .cx 950 958,
  .cx 949 957,
  .ccx 1613 957 949,
  .cx 949 957,
  .cx 1720 956,
  .ccx 1613 956 1720,
  .cx 1720 956,
  .cx 1719 955,
  .ccx 1613 955 1719,
  .cx 1719 955,
  .cx 1718 954,
  .ccx 1613 954 1718,
  .cx 1718 954,
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .x 1613,
  .cx 1597 1613]
private def block2080 : List Gate := [
  .ccx 1576 1724 401,
  .ccx 1576 1613 402,
  .ccx 1562 1724 402,
  .ccx 1562 1613 403,
  .ccx 1563 1724 403,
  .ccx 1563 1613 404,
  .ccx 1564 1724 404,
  .ccx 1564 1613 405,
  .ccx 1565 1724 405,
  .ccx 1565 1613 406,
  .ccx 1566 1724 406,
  .ccx 1566 1613 407,
  .ccx 1567 1724 407,
  .ccx 1567 1613 408,
  .ccx 1568 1724 408,
  .ccx 1568 1613 409,
  .ccx 1569 1724 409,
  .ccx 1569 1613 410,
  .ccx 1570 1724 410,
  .ccx 1570 1613 411,
  .ccx 1571 1724 411,
  .ccx 1571 1613 412,
  .ccx 1572 1724 412,
  .ccx 1572 1613 413,
  .ccx 1573 1724 413,
  .ccx 1573 1613 414,
  .ccx 1574 1724 414,
  .ccx 1574 1613 415,
  .ccx 1575 1724 415,
  .ccx 1575 1613 416,
  .ccx 1560 1724 416,
  .ccx 1560 1613 417]
private def block2112 : List Gate := [
  .cx 1576 1614,
  .cx 1718 401,
  .ccx 1614 401 1718,
  .cx 1562 1614,
  .cx 1719 402,
  .ccx 1614 402 1719,
  .cx 1563 1614,
  .cx 1720 403]
private def block2120 : List Gate := [
  .ccx 1614 403 1720,
  .cx 1564 1614,
  .cx 949 404,
  .ccx 1614 404 949,
  .cx 1565 1614,
  .cx 950 405,
  .ccx 1614 405 950,
  .cx 1566 1614,
  .cx 951 406,
  .ccx 1614 406 951,
  .cx 1567 1614,
  .cx 952 407,
  .ccx 1614 407 952,
  .cx 1568 1614,
  .cx 953 408,
  .ccx 1614 408 953]
private def block2136 : List Gate := [
  .cx 1569 1614,
  .cx 954 409,
  .ccx 1614 409 954,
  .cx 1570 1614,
  .cx 955 410,
  .ccx 1614 410 955,
  .cx 1571 1614,
  .cx 411 956,
  .cx 956 411,
  .ccx 1614 956 411,
  .cx 1572 1614,
  .cx 412 957,
  .cx 957 412,
  .ccx 1614 957 412,
  .cx 1573 1614,
  .cx 413 958,
  .cx 958 413,
  .ccx 1614 958 413,
  .cx 1574 1614,
  .cx 414 959,
  .cx 959 414,
  .ccx 1614 959 414,
  .cx 1575 1614,
  .cx 415 960]
private def block2160 : List Gate := [
  .cx 960 415,
  .ccx 1614 960 415,
  .cx 1560 1614,
  .cx 416 961,
  .cx 961 416,
  .ccx 1614 961 416,
  .cx 417 962,
  .cx 962 417,
  .ccx 1614 962 417,
  .cx 418 963,
  .cx 963 418,
  .ccx 1614 963 418,
  .cx 1560 1614,
  .cx 1575 1614,
  .cx 1574 1614,
  .cx 1573 1614,
  .cx 1572 1614,
  .cx 1571 1614,
  .cx 1570 1614,
  .cx 1569 1614,
  .cx 1568 1614,
  .cx 1567 1614,
  .cx 1566 1614,
  .cx 1565 1614,
  .cx 1564 1614,
  .cx 1563 1614,
  .cx 1562 1614,
  .cx 1576 1614,
  .cx 1597 1613,
  .x 1613,
  .pop 1724 1596 1597,
  .cx 1589 1596,
  .cx 1590 1596,
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596]
private def block2200 : List Gate := [
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .pop 1568 255 1595,
  .pop 1567 1578 1594]
private def block2208 : List Gate := [
  .pop 1566 1580 1593,
  .pop 1565 1582 1592,
  .pop 1564 1584 1591,
  .pop 1563 1586 1590,
  .pop 1562 1588 1589,
  .pop 243 1587 1588,
  .pop 244 1586 1587,
  .pop 245 1585 1586,
  .pop 246 1584 1585,
  .pop 247 1583 1584,
  .pop 248 1582 1583,
  .pop 249 1581 1582,
  .pop 250 1580 1581,
  .pop 251 1579 1580,
  .pop 252 1578 1579,
  .pop 253 1577 1578,
  .pop 254 255 1577,
  .cx 1559 1576,
  .cx 1561 1576,
  .cx 1575 1560,
  .pop 1560 1283 1575,
  .cx 1574 1560,
  .pop 1560 1282 1574,
  .cx 1573 1560]
private def block2232 : List Gate := [
  .pop 1560 1281 1573,
  .cx 1572 1560,
  .pop 1560 1280 1572,
  .cx 1571 1560,
  .pop 1560 1279 1571,
  .cx 1570 1560,
  .pop 1560 1278 1570,
  .cx 1569 1560]
private def block2240 : List Gate := [
  .pop 1560 1277 1569,
  .cx 1568 1560,
  .pop 1560 1276 1568,
  .cx 1567 1560,
  .pop 1560 1275 1567,
  .cx 1566 1560,
  .pop 1560 1274 1566,
  .cx 1565 1560,
  .pop 1560 1273 1565,
  .cx 1564 1560,
  .pop 1560 1272 1564,
  .cx 1563 1560,
  .pop 1560 1271 1563,
  .cx 1562 1560,
  .pop 1560 1270 1562,
  .cx 1561 1560,
  .pop 1560 1269 1561,
  .cx 1721 1560,
  .cx 1559 1560,
  .pop 1721 1722 1559]
private theorem check2240 : bitCheck block2240 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff80002ffffefc000 <<< 1556) := by decide +kernel
private def suffix2240 := block2240 ++ ([]:List Gate)
private theorem valid2240 : bitCheck suffix2240 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff80002ffffefc000 <<< 1556) := bit_join block2240 ([]:List Gate) _ (0x1fffffffffffffff80002ffffefffe8 <<< 1556) _ check2240 rfl
private theorem check2232 : bitCheck block2232 (0x1fffffffffffffff80002ffffefc000 <<< 1556) = some (0x1fffffffffffffff80002ffffec0000 <<< 1556) := by decide +kernel
private def suffix2232 := block2232 ++ suffix2240
private theorem valid2232 : bitCheck suffix2232 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff80002ffffec0000 <<< 1556) := bit_join block2232 suffix2240 _ (0x1fffffffffffffff80002ffffefc000 <<< 1556) _ check2232 valid2240
private theorem check2208 : bitCheck block2208 (0x1fffffffffffffff80002ffffec0000 <<< 1556) = some (0x1fffffffffffffff80002c000000000 <<< 1556) := by decide +kernel
private def suffix2208 := block2208 ++ suffix2232
private theorem valid2208 : bitCheck suffix2208 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff80002c000000000 <<< 1556) := bit_join block2208 suffix2232 _ (0x1fffffffffffffff80002ffffec0000 <<< 1556) _ check2208 valid2232
private theorem check2200 : bitCheck block2200 (0x1fffffffffffffff80002c000000000 <<< 1556) = some (0x1fffffffffffffff800020000000000 <<< 1556) := by decide +kernel
private def suffix2200 := block2200 ++ suffix2208
private theorem valid2200 : bitCheck suffix2200 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800020000000000 <<< 1556) := bit_join block2200 suffix2208 _ (0x1fffffffffffffff80002c000000000 <<< 1556) _ check2200 valid2208
private theorem check2160 : bitCheck block2160 (0x1fffffffffffffff800020000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2160 := block2160 ++ suffix2200
private theorem valid2160 : bitCheck suffix2160 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2160 suffix2200 _ (0x1fffffffffffffff800020000000000 <<< 1556) _ check2160 valid2200
private theorem check2136 : bitCheck block2136 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2136 := block2136 ++ suffix2160
private theorem valid2136 : bitCheck suffix2136 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2136 suffix2160 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2136 valid2160
private theorem check2120 : bitCheck block2120 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2120 := block2120 ++ suffix2136
private theorem valid2120 : bitCheck suffix2120 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2120 suffix2136 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2120 valid2136
private theorem check2112 : bitCheck block2112 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2112 := block2112 ++ suffix2120
private theorem valid2112 : bitCheck suffix2112 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2112 suffix2120 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2112 valid2120
private theorem check2080 : bitCheck block2080 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2080 := block2080 ++ suffix2112
private theorem valid2080 : bitCheck suffix2080 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2080 suffix2112 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2080 valid2112
private theorem check2040 : bitCheck block2040 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2040 := block2040 ++ suffix2080
private theorem valid2040 : bitCheck suffix2040 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2040 suffix2080 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2040 valid2080
private theorem check2016 : bitCheck block2016 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2016 := block2016 ++ suffix2040
private theorem valid2016 : bitCheck suffix2016 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2016 suffix2040 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2016 valid2040
private theorem check2000 : bitCheck block2000 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2000 := block2000 ++ suffix2016
private theorem valid2000 : bitCheck suffix2000 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block2000 suffix2016 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check2000 valid2016
private theorem check1960 : bitCheck block1960 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1960 := block1960 ++ suffix2000
private theorem valid1960 : bitCheck suffix1960 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1960 suffix2000 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1960 valid2000
private theorem check1944 : bitCheck block1944 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1944 := block1944 ++ suffix1960
private theorem valid1944 : bitCheck suffix1944 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1944 suffix1960 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1944 valid1960
private theorem check1920 : bitCheck block1920 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1920 := block1920 ++ suffix1944
private theorem valid1920 : bitCheck suffix1920 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1920 suffix1944 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1920 valid1944
private theorem check1880 : bitCheck block1880 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1880 := block1880 ++ suffix1920
private theorem valid1880 : bitCheck suffix1880 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1880 suffix1920 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1880 valid1920
private theorem check1848 : bitCheck block1848 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1848 := block1848 ++ suffix1880
private theorem valid1848 : bitCheck suffix1848 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1848 suffix1880 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1848 valid1880
private theorem check1840 : bitCheck block1840 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1840 := block1840 ++ suffix1848
private theorem valid1840 : bitCheck suffix1840 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1840 suffix1848 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1840 valid1848
private theorem check1824 : bitCheck block1824 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1824 := block1824 ++ suffix1840
private theorem valid1824 : bitCheck suffix1824 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1824 suffix1840 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1824 valid1840
private theorem check1800 : bitCheck block1800 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1800 := block1800 ++ suffix1824
private theorem valid1800 : bitCheck suffix1800 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1800 suffix1824 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1800 valid1824
private theorem check1760 : bitCheck block1760 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1760 := block1760 ++ suffix1800
private theorem valid1760 : bitCheck suffix1760 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1760 suffix1800 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1760 valid1800
private theorem check1752 : bitCheck block1752 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1752 := block1752 ++ suffix1760
private theorem valid1752 : bitCheck suffix1752 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1752 suffix1760 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1752 valid1760
private theorem check1728 : bitCheck block1728 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1728 := block1728 ++ suffix1752
private theorem valid1728 : bitCheck suffix1728 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1728 suffix1752 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1728 valid1752
private theorem check1720 : bitCheck block1720 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1720 := block1720 ++ suffix1728
private theorem valid1720 : bitCheck suffix1720 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1720 suffix1728 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1720 valid1728
private theorem check1680 : bitCheck block1680 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1680 := block1680 ++ suffix1720
private theorem valid1680 : bitCheck suffix1680 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1680 suffix1720 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1680 valid1720
private theorem check1656 : bitCheck block1656 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1656 := block1656 ++ suffix1680
private theorem valid1656 : bitCheck suffix1656 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1656 suffix1680 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1656 valid1680
private theorem check1640 : bitCheck block1640 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1640 := block1640 ++ suffix1656
private theorem valid1640 : bitCheck suffix1640 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1640 suffix1656 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1640 valid1656
private theorem check1632 : bitCheck block1632 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1632 := block1632 ++ suffix1640
private theorem valid1632 : bitCheck suffix1632 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1632 suffix1640 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1632 valid1640
private theorem check1600 : bitCheck block1600 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1600 := block1600 ++ suffix1632
private theorem valid1600 : bitCheck suffix1600 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1600 suffix1632 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1600 valid1632
private theorem check1560 : bitCheck block1560 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1560 := block1560 ++ suffix1600
private theorem valid1560 : bitCheck suffix1560 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1560 suffix1600 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1560 valid1600
private theorem check1536 : bitCheck block1536 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1536 := block1536 ++ suffix1560
private theorem valid1536 : bitCheck suffix1536 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1536 suffix1560 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1536 valid1560
private theorem check1520 : bitCheck block1520 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1520 := block1520 ++ suffix1536
private theorem valid1520 : bitCheck suffix1520 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1520 suffix1536 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1520 valid1536
private theorem check1480 : bitCheck block1480 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1480 := block1480 ++ suffix1520
private theorem valid1480 : bitCheck suffix1480 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1480 suffix1520 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1480 valid1520
private theorem check1464 : bitCheck block1464 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1464 := block1464 ++ suffix1480
private theorem valid1464 : bitCheck suffix1464 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1464 suffix1480 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1464 valid1480
private theorem check1440 : bitCheck block1440 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1440 := block1440 ++ suffix1464
private theorem valid1440 : bitCheck suffix1440 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1440 suffix1464 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1440 valid1464
private theorem check1400 : bitCheck block1400 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1400 := block1400 ++ suffix1440
private theorem valid1400 : bitCheck suffix1400 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1400 suffix1440 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1400 valid1440
private theorem check1368 : bitCheck block1368 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1368 := block1368 ++ suffix1400
private theorem valid1368 : bitCheck suffix1368 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1368 suffix1400 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1368 valid1400
private theorem check1360 : bitCheck block1360 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1360 := block1360 ++ suffix1368
private theorem valid1360 : bitCheck suffix1360 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1360 suffix1368 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1360 valid1368
private theorem check1344 : bitCheck block1344 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1344 := block1344 ++ suffix1360
private theorem valid1344 : bitCheck suffix1344 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1344 suffix1360 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1344 valid1360
private theorem check1320 : bitCheck block1320 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1320 := block1320 ++ suffix1344
private theorem valid1320 : bitCheck suffix1320 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1320 suffix1344 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1320 valid1344
private theorem check1280 : bitCheck block1280 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1280 := block1280 ++ suffix1320
private theorem valid1280 : bitCheck suffix1280 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1280 suffix1320 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1280 valid1320
private theorem check1272 : bitCheck block1272 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1272 := block1272 ++ suffix1280
private theorem valid1272 : bitCheck suffix1272 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1272 suffix1280 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1272 valid1280
private theorem check1248 : bitCheck block1248 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1248 := block1248 ++ suffix1272
private theorem valid1248 : bitCheck suffix1248 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1248 suffix1272 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1248 valid1272
private theorem check1240 : bitCheck block1240 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1240 := block1240 ++ suffix1248
private theorem valid1240 : bitCheck suffix1240 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1240 suffix1248 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1240 valid1248
private theorem check1200 : bitCheck block1200 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1200 := block1200 ++ suffix1240
private theorem valid1200 : bitCheck suffix1200 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1200 suffix1240 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1200 valid1240
private theorem check1176 : bitCheck block1176 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1176 := block1176 ++ suffix1200
private theorem valid1176 : bitCheck suffix1176 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1176 suffix1200 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1176 valid1200
private theorem check1160 : bitCheck block1160 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1160 := block1160 ++ suffix1176
private theorem valid1160 : bitCheck suffix1160 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1160 suffix1176 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1160 valid1176
private theorem check1152 : bitCheck block1152 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1152 := block1152 ++ suffix1160
private theorem valid1152 : bitCheck suffix1152 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1152 suffix1160 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1152 valid1160
private theorem check1120 : bitCheck block1120 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1120 := block1120 ++ suffix1152
private theorem valid1120 : bitCheck suffix1120 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1120 suffix1152 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1120 valid1152
private theorem check1080 : bitCheck block1080 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1080 := block1080 ++ suffix1120
private theorem valid1080 : bitCheck suffix1080 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1080 suffix1120 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1080 valid1120
private theorem check1056 : bitCheck block1056 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1056 := block1056 ++ suffix1080
private theorem valid1056 : bitCheck suffix1056 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1056 suffix1080 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1056 valid1080
private theorem check1040 : bitCheck block1040 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1040 := block1040 ++ suffix1056
private theorem valid1040 : bitCheck suffix1040 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1040 suffix1056 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1040 valid1056
private theorem check1000 : bitCheck block1000 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1000 := block1000 ++ suffix1040
private theorem valid1000 : bitCheck suffix1000 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block1000 suffix1040 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check1000 valid1040
private theorem check984 : bitCheck block984 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix984 := block984 ++ suffix1000
private theorem valid984 : bitCheck suffix984 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block984 suffix1000 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check984 valid1000
private theorem check960 : bitCheck block960 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix960 := block960 ++ suffix984
private theorem valid960 : bitCheck suffix960 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block960 suffix984 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check960 valid984
private theorem check920 : bitCheck block920 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix920 := block920 ++ suffix960
private theorem valid920 : bitCheck suffix920 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block920 suffix960 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check920 valid960
private theorem check888 : bitCheck block888 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix888 := block888 ++ suffix920
private theorem valid888 : bitCheck suffix888 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block888 suffix920 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check888 valid920
private theorem check880 : bitCheck block880 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix880 := block880 ++ suffix888
private theorem valid880 : bitCheck suffix880 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block880 suffix888 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check880 valid888
private theorem check864 : bitCheck block864 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix864 := block864 ++ suffix880
private theorem valid864 : bitCheck suffix864 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block864 suffix880 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check864 valid880
private theorem check840 : bitCheck block840 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix840 := block840 ++ suffix864
private theorem valid840 : bitCheck suffix840 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block840 suffix864 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check840 valid864
private theorem check800 : bitCheck block800 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix800 := block800 ++ suffix840
private theorem valid800 : bitCheck suffix800 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block800 suffix840 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check800 valid840
private theorem check792 : bitCheck block792 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix792 := block792 ++ suffix800
private theorem valid792 : bitCheck suffix792 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block792 suffix800 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check792 valid800
private theorem check768 : bitCheck block768 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix768 := block768 ++ suffix792
private theorem valid768 : bitCheck suffix768 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block768 suffix792 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check768 valid792
private theorem check760 : bitCheck block760 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix760 := block760 ++ suffix768
private theorem valid760 : bitCheck suffix760 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block760 suffix768 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check760 valid768
private theorem check720 : bitCheck block720 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix720 := block720 ++ suffix760
private theorem valid720 : bitCheck suffix720 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block720 suffix760 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check720 valid760
private theorem check696 : bitCheck block696 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix696 := block696 ++ suffix720
private theorem valid696 : bitCheck suffix696 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffff800000000000000 <<< 1556) := bit_join block696 suffix720 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check696 valid720
private theorem check680 : bitCheck block680 (0x1fffffffffffffff800000000000000 <<< 1556) = some (0x1ffffffffffffffc000000000000000 <<< 1556) := by decide +kernel
private def suffix680 := block680 ++ suffix696
private theorem valid680 : bitCheck suffix680 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1ffffffffffffffc000000000000000 <<< 1556) := bit_join block680 suffix696 _ (0x1fffffffffffffff800000000000000 <<< 1556) _ check680 valid696
private theorem check672 : bitCheck block672 (0x1ffffffffffffffc000000000000000 <<< 1556) = some (0x1fffffffffffffc0000000000000000 <<< 1556) := by decide +kernel
private def suffix672 := block672 ++ suffix680
private theorem valid672 : bitCheck suffix672 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffffffc0000000000000000 <<< 1556) := bit_join block672 suffix680 _ (0x1ffffffffffffffc000000000000000 <<< 1556) _ check672 valid680
private theorem check640 : bitCheck block640 (0x1fffffffffffffc0000000000000000 <<< 1556) = some (0x1fffffffffc00000000000000000000 <<< 1556) := by decide +kernel
private def suffix640 := block640 ++ suffix672
private theorem valid640 : bitCheck suffix640 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fffffffffc00000000000000000000 <<< 1556) := bit_join block640 suffix672 _ (0x1fffffffffffffc0000000000000000 <<< 1556) _ check640 valid672
private theorem check600 : bitCheck block600 (0x1fffffffffc00000000000000000000 <<< 1556) = some (0x1ffffc0000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix600 := block600 ++ suffix640
private theorem valid600 : bitCheck suffix600 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1ffffc0000000000000000000000000 <<< 1556) := bit_join block600 suffix640 _ (0x1fffffffffc00000000000000000000 <<< 1556) _ check600 valid640
private theorem check576 : bitCheck block576 (0x1ffffc0000000000000000000000000 <<< 1556) = some (0x1fc0000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix576 := block576 ++ suffix600
private theorem valid576 : bitCheck suffix576 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x1fc0000000000000000000000000000 <<< 1556) := bit_join block576 suffix600 _ (0x1ffffc0000000000000000000000000 <<< 1556) _ check576 valid600
private theorem check560 : bitCheck block560 (0x1fc0000000000000000000000000000 <<< 1556) = some 0 := by decide +kernel
private def suffix560 := block560 ++ suffix576
private theorem valid560 : bitCheck suffix560 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some 0 := bit_join block560 suffix576 _ (0x1fc0000000000000000000000000000 <<< 1556) _ check560 valid576
private theorem check520 : bitCheck block520 0 = some (0x3f800000000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix520 := block520 ++ suffix560
private theorem valid520 : bitCheck suffix520 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3f800000000000000000000000000000000 <<< 1556) := bit_join block520 suffix560 _ 0 _ check520 valid560
private theorem check504 : bitCheck block504 (0x3f800000000000000000000000000000000 <<< 1556) = some (0x3fffff80000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix504 := block504 ++ suffix520
private theorem valid504 : bitCheck suffix504 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffff80000000000000000000000000000 <<< 1556) := bit_join block504 suffix520 _ (0x3f800000000000000000000000000000000 <<< 1556) _ check504 valid520
private theorem check480 : bitCheck block480 (0x3fffff80000000000000000000000000000 <<< 1556) = some (0x3fffffffffff80000000000000000000000 <<< 1556) := by decide +kernel
private def suffix480 := block480 ++ suffix504
private theorem valid480 : bitCheck suffix480 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffff80000000000000000000000 <<< 1556) := bit_join block480 suffix504 _ (0x3fffff80000000000000000000000000000 <<< 1556) _ check480 valid504
private theorem check440 : bitCheck block440 (0x3fffffffffff80000000000000000000000 <<< 1556) = some (0x3fffffffffffffffffffff8000000000000 <<< 1556) := by decide +kernel
private def suffix440 := block440 ++ suffix480
private theorem valid440 : bitCheck suffix440 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffff8000000000000 <<< 1556) := bit_join block440 suffix480 _ (0x3fffffffffff80000000000000000000000 <<< 1556) _ check440 valid480
private theorem check408 : bitCheck block408 (0x3fffffffffffffffffffff8000000000000 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix408 := block408 ++ suffix440
private theorem valid408 : bitCheck suffix408 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block408 suffix440 _ (0x3fffffffffffffffffffff8000000000000 <<< 1556) _ check408 valid440
private theorem check400 : bitCheck block400 (0x3fffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix400 := block400 ++ suffix408
private theorem valid400 : bitCheck suffix400 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block400 suffix408 _ (0x3fffffffffffffffffffffffc0000000000 <<< 1556) _ check400 valid408
private theorem check384 : bitCheck block384 (0x3fffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix384 := block384 ++ suffix400
private theorem valid384 : bitCheck suffix384 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block384 suffix400 _ (0x3fffffffffffffffffffffffc0000000000 <<< 1556) _ check384 valid400
private theorem check360 : bitCheck block360 (0x3fffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix360 := block360 ++ suffix384
private theorem valid360 : bitCheck suffix360 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block360 suffix384 _ (0x3fffffffffffffffffffffffc0000000000 <<< 1556) _ check360 valid384
private theorem check320 : bitCheck block320 (0x3fffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffe0000000000 <<< 1556) := by decide +kernel
private def suffix320 := block320 ++ suffix360
private theorem valid320 : bitCheck suffix320 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffe0000000000 <<< 1556) := bit_join block320 suffix360 _ (0x3fffffffffffffffffffffffc0000000000 <<< 1556) _ check320 valid360
private theorem check312 : bitCheck block312 (0x3fffffffffffffffffffffffe0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffe0000000000 <<< 1556) := by decide +kernel
private def suffix312 := block312 ++ suffix320
private theorem valid312 : bitCheck suffix312 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffe0000000000 <<< 1556) := bit_join block312 suffix320 _ (0x3fffffffffffffffffffffffe0000000000 <<< 1556) _ check312 valid320
private theorem check288 : bitCheck block288 (0x3fffffffffffffffffffffffe0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffefffc000000 <<< 1556) := by decide +kernel
private def suffix288 := block288 ++ suffix312
private theorem valid288 : bitCheck suffix288 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffefffc000000 <<< 1556) := bit_join block288 suffix312 _ (0x3fffffffffffffffffffffffe0000000000 <<< 1556) _ check288 valid312
private theorem check280 : bitCheck block280 (0x3fffffffffffffffffffffffefffc000000 <<< 1556) = some (0x3fffffffffffffffffffffffeffffe00000 <<< 1556) := by decide +kernel
private def suffix280 := block280 ++ suffix288
private theorem valid280 : bitCheck suffix280 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffe00000 <<< 1556) := bit_join block280 suffix288 _ (0x3fffffffffffffffffffffffefffc000000 <<< 1556) _ check280 valid288
private theorem check240 : bitCheck block240 (0x3fffffffffffffffffffffffeffffe00000 <<< 1556) = some (0x3fffffffffffffffffffffffeffffefffe8 <<< 1556) := by decide +kernel
private def suffix240 := block240 ++ suffix280
private theorem valid240 : bitCheck suffix240 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffefffe8 <<< 1556) := bit_join block240 suffix280 _ (0x3fffffffffffffffffffffffeffffe00000 <<< 1556) _ check240 valid280
private theorem check216 : bitCheck block216 (0x3fffffffffffffffffffffffeffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffefff80 <<< 1556) := by decide +kernel
private def suffix216 := block216 ++ suffix240
private theorem valid216 : bitCheck suffix216 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffefff80 <<< 1556) := bit_join block216 suffix240 _ (0x3fffffffffffffffffffffffeffffefffe8 <<< 1556) _ check216 valid240
private theorem check200 : bitCheck block200 (0x3fffffffffffffffffffffffeffffefff80 <<< 1556) = some (0x3fffffffffffffffffffffffeffffef8000 <<< 1556) := by decide +kernel
private def suffix200 := block200 ++ suffix216
private theorem valid200 : bitCheck suffix200 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffef8000 <<< 1556) := bit_join block200 suffix216 _ (0x3fffffffffffffffffffffffeffffefff80 <<< 1556) _ check200 valid216
private theorem check192 : bitCheck block192 (0x3fffffffffffffffffffffffeffffef8000 <<< 1556) = some (0x3fffffffffffffffffffffffeffffe80000 <<< 1556) := by decide +kernel
private def suffix192 := block192 ++ suffix200
private theorem valid192 : bitCheck suffix192 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffe80000 <<< 1556) := bit_join block192 suffix200 _ (0x3fffffffffffffffffffffffeffffef8000 <<< 1556) _ check192 valid200
private theorem check160 : bitCheck block160 (0x3fffffffffffffffffffffffeffffe80000 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffc <<< 1556) := by decide +kernel
private def suffix160 := block160 ++ suffix192
private theorem valid160 : bitCheck suffix160 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffc <<< 1556) := bit_join block160 suffix192 _ (0x3fffffffffffffffffffffffeffffe80000 <<< 1556) _ check160 valid192
private theorem check120 : bitCheck block120 (0x3fffffffffffffffffffffffeffffeffffc <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffe00 <<< 1556) := by decide +kernel
private def suffix120 := block120 ++ suffix160
private theorem valid120 : bitCheck suffix120 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffe00 <<< 1556) := bit_join block120 suffix160 _ (0x3fffffffffffffffffffffffeffffeffffc <<< 1556) _ check120 valid160
private theorem check96 : bitCheck block96 (0x3fffffffffffffffffffffffeffffeffe00 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix96 := block96 ++ suffix120
private theorem valid96 : bitCheck suffix96 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block96 suffix120 _ (0x3fffffffffffffffffffffffeffffeffe00 <<< 1556) _ check96 valid120
private theorem check80 : bitCheck block80 (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix80 := block80 ++ suffix96
private theorem valid80 : bitCheck suffix80 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block80 suffix96 _ (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) _ check80 valid96
private theorem check40 : bitCheck block40 (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix40 := block40 ++ suffix80
private theorem valid40 : bitCheck suffix40 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block40 suffix80 _ (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) _ check40 valid80
private theorem check24 : bitCheck block24 (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix24 := block24 ++ suffix40
private theorem valid24 : bitCheck suffix24 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block24 suffix40 _ (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) _ check24 valid40
private theorem check0 : bitCheck block0 (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix0 := block0 ++ suffix24
private theorem valid0 : bitCheck suffix0 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block0 suffix24 _ (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) _ check0 valid24
private def group0 := suffix0
private theorem cert0 : bitCheck group0 (0x1fffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffeffffeffffe <<< 1556) := valid0
private def ops := group0 ++ (group1 ++ group2)
private theorem fPart0 : Partial.leave225Part0 = GateMirror.forward block0 ++ GateMirror.forward block24 ++ GateMirror.forward block40 ++ GateMirror.forward block80 := by rfl
private theorem fPart1 : Partial.leave225Part1 = GateMirror.forward block96 ++ GateMirror.forward block120 ++ GateMirror.forward block160 := by rfl
private theorem fPart2 : Partial.leave225Part2 = GateMirror.forward block192 ++ GateMirror.forward block200 ++ GateMirror.forward block216 ++ GateMirror.forward block240 ++ GateMirror.forward block280 := by rfl
private theorem fPart3 : Partial.leave225Part3 = GateMirror.forward block288 ++ GateMirror.forward block312 ++ GateMirror.forward block320 ++ GateMirror.forward block360 := by rfl
private theorem fPart4 : Partial.leave225Part4 = GateMirror.forward block384 ++ GateMirror.forward block400 ++ GateMirror.forward block408 ++ GateMirror.forward block440 := by rfl
private theorem fPart5 : Partial.leave225Part5 = GateMirror.forward block480 ++ GateMirror.forward block504 ++ GateMirror.forward block520 ++ GateMirror.forward block560 := by rfl
private theorem fPart6 : Partial.leave225Part6 = GateMirror.forward block576 ++ GateMirror.forward block600 ++ GateMirror.forward block640 := by rfl
private theorem fPart7 : Partial.leave225Part7 = GateMirror.forward block672 ++ GateMirror.forward block680 ++ GateMirror.forward block696 ++ GateMirror.forward block720 ++ GateMirror.forward block760 := by rfl
private theorem fPart8 : Partial.leave225Part8 = GateMirror.forward block768 ++ GateMirror.forward block792 ++ GateMirror.forward block800 ++ GateMirror.forward block840 := by rfl
private theorem fPart9 : Partial.leave225Part9 = GateMirror.forward block864 ++ GateMirror.forward block880 ++ GateMirror.forward block888 ++ GateMirror.forward block920 := by rfl
private theorem fPart10 : Partial.leave225Part10 = GateMirror.forward block960 ++ GateMirror.forward block984 ++ GateMirror.forward block1000 ++ GateMirror.forward block1040 := by rfl
private theorem fPart11 : Partial.leave225Part11 = GateMirror.forward block1056 ++ GateMirror.forward block1080 ++ GateMirror.forward block1120 := by rfl
private theorem fPart12 : Partial.leave225Part12 = GateMirror.forward block1152 ++ GateMirror.forward block1160 ++ GateMirror.forward block1176 ++ GateMirror.forward block1200 ++ GateMirror.forward block1240 := by rfl
private theorem fPart13 : Partial.leave225Part13 = GateMirror.forward block1248 ++ GateMirror.forward block1272 ++ GateMirror.forward block1280 ++ GateMirror.forward block1320 := by rfl
private theorem fPart14 : Partial.leave225Part14 = GateMirror.forward block1344 ++ GateMirror.forward block1360 ++ GateMirror.forward block1368 ++ GateMirror.forward block1400 := by rfl
private theorem fPart15 : Partial.leave225Part15 = GateMirror.forward block1440 ++ GateMirror.forward block1464 ++ GateMirror.forward block1480 ++ GateMirror.forward block1520 := by rfl
private theorem fPart16 : Partial.leave225Part16 = GateMirror.forward block1536 ++ GateMirror.forward block1560 ++ GateMirror.forward block1600 := by rfl
private theorem fPart17 : Partial.leave225Part17 = GateMirror.forward block1632 ++ GateMirror.forward block1640 ++ GateMirror.forward block1656 ++ GateMirror.forward block1680 ++ GateMirror.forward block1720 := by rfl
private theorem fPart18 : Partial.leave225Part18 = GateMirror.forward block1728 ++ GateMirror.forward block1752 ++ GateMirror.forward block1760 ++ GateMirror.forward block1800 := by rfl
private theorem fPart19 : Partial.leave225Part19 = GateMirror.forward block1824 ++ GateMirror.forward block1840 ++ GateMirror.forward block1848 ++ GateMirror.forward block1880 := by rfl
private theorem fPart20 : Partial.leave225Part20 = GateMirror.forward block1920 ++ GateMirror.forward block1944 ++ GateMirror.forward block1960 ++ GateMirror.forward block2000 := by rfl
private theorem fPart21 : Partial.leave225Part21 = GateMirror.forward block2016 ++ GateMirror.forward block2040 ++ GateMirror.forward block2080 := by rfl
private theorem fPart22 : Partial.leave225Part22 = GateMirror.forward block2112 ++ GateMirror.forward block2120 ++ GateMirror.forward block2136 ++ GateMirror.forward block2160 ++ GateMirror.forward block2200 := by rfl
private theorem fPart23 : Partial.leave225Part23 = GateMirror.forward block2208 ++ GateMirror.forward block2232 ++ GateMirror.forward block2240 ++ GateMirror.forward block2260 ++ GateMirror.forward block2300 := by rfl
private theorem fPart24 : Partial.leave225Part24 = GateMirror.forward block2304 ++ GateMirror.forward block2328 ++ GateMirror.forward block2340 ++ GateMirror.forward block2380 := by rfl
private theorem fPart25 : Partial.leave225Part25 = GateMirror.forward block2400 ++ GateMirror.forward block2420 ++ GateMirror.forward block2424 ++ GateMirror.forward block2460 := by rfl
private theorem fPart26 : Partial.leave225Part26 = GateMirror.forward block2496 ++ GateMirror.forward block2500 ++ GateMirror.forward block2520 ++ GateMirror.forward block2540 ++ GateMirror.forward block2580 := by rfl
private theorem fPart27 : Partial.leave225Part27 = GateMirror.forward block2592 ++ GateMirror.forward block2616 ++ GateMirror.forward block2620 ++ GateMirror.forward block2660 := by rfl
private theorem fPart28 : Partial.leave225Part28 = GateMirror.forward block2688 ++ GateMirror.forward block2700 ++ GateMirror.forward block2712 ++ GateMirror.forward block2740 ++ GateMirror.forward block2780 := by rfl
private theorem fPart29 : Partial.leave225Part29 = GateMirror.forward block2784 ++ GateMirror.forward block2808 ++ GateMirror.forward block2820 ++ GateMirror.forward block2847 := by rfl
private theorem fPart30 : Partial.leave225Part30 = GateMirror.forward block2880 ++ GateMirror.forward block2887 ++ GateMirror.forward block2904 ++ GateMirror.forward block2927 ++ GateMirror.forward block2967 := by rfl
private theorem fPart31 : Partial.leave225Part31 = GateMirror.forward block2976 ++ GateMirror.forward block3000 ++ GateMirror.forward block3007 ++ GateMirror.forward block3047 := by rfl
private theorem fPart32 : Partial.leave225Part32 = GateMirror.forward block3072 ++ GateMirror.forward block3087 ++ GateMirror.forward block3096 ++ GateMirror.forward block3127 ++ GateMirror.forward block3167 := by rfl
private theorem fPart33 : Partial.leave225Part33 = GateMirror.forward block3168 := by rfl
private theorem fEq : GateMirror.forward ops = Partial.leave225 := by
  simp only [ops,group0,group1,group2,suffix0,suffix24,suffix40,suffix80,suffix96,suffix120,suffix160,suffix192,suffix200,suffix216,suffix240,suffix280,suffix288,suffix312,suffix320,suffix360,suffix384,suffix400,suffix408,suffix440,suffix480,suffix504,suffix520,suffix560,suffix576,suffix600,suffix640,suffix672,suffix680,suffix696,suffix720,suffix760,suffix768,suffix792,suffix800,suffix840,suffix864,suffix880,suffix888,suffix920,suffix960,suffix984,suffix1000,suffix1040,suffix1056,suffix1080,suffix1120,suffix1152,suffix1160,suffix1176,suffix1200,suffix1240,suffix1248,suffix1272,suffix1280,suffix1320,suffix1344,suffix1360,suffix1368,suffix1400,suffix1440,suffix1464,suffix1480,suffix1520,suffix1536,suffix1560,suffix1600,suffix1632,suffix1640,suffix1656,suffix1680,suffix1720,suffix1728,suffix1752,suffix1760,suffix1800,suffix1824,suffix1840,suffix1848,suffix1880,suffix1920,suffix1944,suffix1960,suffix2000,suffix2016,suffix2040,suffix2080,suffix2112,suffix2120,suffix2136,suffix2160,suffix2200,suffix2208,suffix2232,suffix2240,suffix2260,suffix2300,suffix2304,suffix2328,suffix2340,suffix2380,suffix2400,suffix2420,suffix2424,suffix2460,suffix2496,suffix2500,suffix2520,suffix2540,suffix2580,suffix2592,suffix2616,suffix2620,suffix2660,suffix2688,suffix2700,suffix2712,suffix2740,suffix2780,suffix2784,suffix2808,suffix2820,suffix2847,suffix2880,suffix2887,suffix2904,suffix2927,suffix2967,suffix2976,suffix3000,suffix3007,suffix3047,suffix3072,suffix3087,suffix3096,suffix3127,suffix3167,suffix3168,fwAppend,List.append_nil,Partial.leave225,fPart0,fPart1,fPart2,fPart3,fPart4,fPart5,fPart6,fPart7,fPart8,fPart9,fPart10,fPart11,fPart12,fPart13,fPart14,fPart15,fPart16,fPart17,fPart18,fPart19,fPart20,fPart21,fPart22,fPart23,fPart24,fPart25,fPart26,fPart27,fPart28,fPart29,fPart30,fPart31,fPart32,fPart33,List.append_assoc]
private theorem bPart0 : Partial.leave225InvPart0 = GateMirror.inverse block3168 ++ GateMirror.inverse block3167 ++ GateMirror.inverse block3127 ++ GateMirror.inverse block3096 := by rfl
private theorem bPart1 : Partial.leave225InvPart1 = GateMirror.inverse block3087 ++ GateMirror.inverse block3072 ++ GateMirror.inverse block3047 ++ GateMirror.inverse block3007 ++ GateMirror.inverse block3000 := by rfl
private theorem bPart2 : Partial.leave225InvPart2 = GateMirror.inverse block2976 ++ GateMirror.inverse block2967 ++ GateMirror.inverse block2927 ++ GateMirror.inverse block2904 := by rfl
private theorem bPart3 : Partial.leave225InvPart3 = GateMirror.inverse block2887 ++ GateMirror.inverse block2880 ++ GateMirror.inverse block2847 ++ GateMirror.inverse block2820 ++ GateMirror.inverse block2808 := by rfl
private theorem bPart4 : Partial.leave225InvPart4 = GateMirror.inverse block2784 ++ GateMirror.inverse block2780 ++ GateMirror.inverse block2740 ++ GateMirror.inverse block2712 := by rfl
private theorem bPart5 : Partial.leave225InvPart5 = GateMirror.inverse block2700 ++ GateMirror.inverse block2688 ++ GateMirror.inverse block2660 ++ GateMirror.inverse block2620 ++ GateMirror.inverse block2616 := by rfl
private theorem bPart6 : Partial.leave225InvPart6 = GateMirror.inverse block2592 ++ GateMirror.inverse block2580 ++ GateMirror.inverse block2540 ++ GateMirror.inverse block2520 := by rfl
private theorem bPart7 : Partial.leave225InvPart7 = GateMirror.inverse block2500 ++ GateMirror.inverse block2496 ++ GateMirror.inverse block2460 ++ GateMirror.inverse block2424 := by rfl
private theorem bPart8 : Partial.leave225InvPart8 = GateMirror.inverse block2420 ++ GateMirror.inverse block2400 ++ GateMirror.inverse block2380 ++ GateMirror.inverse block2340 ++ GateMirror.inverse block2328 := by rfl
private theorem bPart9 : Partial.leave225InvPart9 = GateMirror.inverse block2304 ++ GateMirror.inverse block2300 ++ GateMirror.inverse block2260 ++ GateMirror.inverse block2240 ++ GateMirror.inverse block2232 := by rfl
private theorem bPart10 : Partial.leave225InvPart10 = GateMirror.inverse block2208 ++ GateMirror.inverse block2200 ++ GateMirror.inverse block2160 ++ GateMirror.inverse block2136 := by rfl
private theorem bPart11 : Partial.leave225InvPart11 = GateMirror.inverse block2120 ++ GateMirror.inverse block2112 ++ GateMirror.inverse block2080 ++ GateMirror.inverse block2040 := by rfl
private theorem bPart12 : Partial.leave225InvPart12 = GateMirror.inverse block2016 ++ GateMirror.inverse block2000 ++ GateMirror.inverse block1960 ++ GateMirror.inverse block1944 := by rfl
private theorem bPart13 : Partial.leave225InvPart13 = GateMirror.inverse block1920 ++ GateMirror.inverse block1880 ++ GateMirror.inverse block1848 := by rfl
private theorem bPart14 : Partial.leave225InvPart14 = GateMirror.inverse block1840 ++ GateMirror.inverse block1824 ++ GateMirror.inverse block1800 ++ GateMirror.inverse block1760 ++ GateMirror.inverse block1752 := by rfl
private theorem bPart15 : Partial.leave225InvPart15 = GateMirror.inverse block1728 ++ GateMirror.inverse block1720 ++ GateMirror.inverse block1680 ++ GateMirror.inverse block1656 := by rfl
private theorem bPart16 : Partial.leave225InvPart16 = GateMirror.inverse block1640 ++ GateMirror.inverse block1632 ++ GateMirror.inverse block1600 ++ GateMirror.inverse block1560 := by rfl
private theorem bPart17 : Partial.leave225InvPart17 = GateMirror.inverse block1536 ++ GateMirror.inverse block1520 ++ GateMirror.inverse block1480 ++ GateMirror.inverse block1464 := by rfl
private theorem bPart18 : Partial.leave225InvPart18 = GateMirror.inverse block1440 ++ GateMirror.inverse block1400 ++ GateMirror.inverse block1368 := by rfl
private theorem bPart19 : Partial.leave225InvPart19 = GateMirror.inverse block1360 ++ GateMirror.inverse block1344 ++ GateMirror.inverse block1320 ++ GateMirror.inverse block1280 ++ GateMirror.inverse block1272 := by rfl
private theorem bPart20 : Partial.leave225InvPart20 = GateMirror.inverse block1248 ++ GateMirror.inverse block1240 ++ GateMirror.inverse block1200 ++ GateMirror.inverse block1176 := by rfl
private theorem bPart21 : Partial.leave225InvPart21 = GateMirror.inverse block1160 ++ GateMirror.inverse block1152 ++ GateMirror.inverse block1120 ++ GateMirror.inverse block1080 := by rfl
private theorem bPart22 : Partial.leave225InvPart22 = GateMirror.inverse block1056 ++ GateMirror.inverse block1040 ++ GateMirror.inverse block1000 ++ GateMirror.inverse block984 := by rfl
private theorem bPart23 : Partial.leave225InvPart23 = GateMirror.inverse block960 ++ GateMirror.inverse block920 ++ GateMirror.inverse block888 := by rfl
private theorem bPart24 : Partial.leave225InvPart24 = GateMirror.inverse block880 ++ GateMirror.inverse block864 ++ GateMirror.inverse block840 ++ GateMirror.inverse block800 ++ GateMirror.inverse block792 := by rfl
private theorem bPart25 : Partial.leave225InvPart25 = GateMirror.inverse block768 ++ GateMirror.inverse block760 ++ GateMirror.inverse block720 ++ GateMirror.inverse block696 := by rfl
private theorem bPart26 : Partial.leave225InvPart26 = GateMirror.inverse block680 ++ GateMirror.inverse block672 ++ GateMirror.inverse block640 ++ GateMirror.inverse block600 := by rfl
private theorem bPart27 : Partial.leave225InvPart27 = GateMirror.inverse block576 ++ GateMirror.inverse block560 ++ GateMirror.inverse block520 ++ GateMirror.inverse block504 := by rfl
private theorem bPart28 : Partial.leave225InvPart28 = GateMirror.inverse block480 ++ GateMirror.inverse block440 ++ GateMirror.inverse block408 := by rfl
private theorem bPart29 : Partial.leave225InvPart29 = GateMirror.inverse block400 ++ GateMirror.inverse block384 ++ GateMirror.inverse block360 ++ GateMirror.inverse block320 ++ GateMirror.inverse block312 := by rfl
private theorem bPart30 : Partial.leave225InvPart30 = GateMirror.inverse block288 ++ GateMirror.inverse block280 ++ GateMirror.inverse block240 ++ GateMirror.inverse block216 := by rfl
private theorem bPart31 : Partial.leave225InvPart31 = GateMirror.inverse block200 ++ GateMirror.inverse block192 ++ GateMirror.inverse block160 ++ GateMirror.inverse block120 := by rfl
private theorem bPart32 : Partial.leave225InvPart32 = GateMirror.inverse block96 ++ GateMirror.inverse block80 ++ GateMirror.inverse block40 ++ GateMirror.inverse block24 := by rfl
private theorem bPart33 : Partial.leave225InvPart33 = GateMirror.inverse block0 := by rfl
private theorem bEq : GateMirror.inverse ops = Partial.leave225Inv := by
  simp only [ops,group0,group1,group2,suffix0,suffix24,suffix40,suffix80,suffix96,suffix120,suffix160,suffix192,suffix200,suffix216,suffix240,suffix280,suffix288,suffix312,suffix320,suffix360,suffix384,suffix400,suffix408,suffix440,suffix480,suffix504,suffix520,suffix560,suffix576,suffix600,suffix640,suffix672,suffix680,suffix696,suffix720,suffix760,suffix768,suffix792,suffix800,suffix840,suffix864,suffix880,suffix888,suffix920,suffix960,suffix984,suffix1000,suffix1040,suffix1056,suffix1080,suffix1120,suffix1152,suffix1160,suffix1176,suffix1200,suffix1240,suffix1248,suffix1272,suffix1280,suffix1320,suffix1344,suffix1360,suffix1368,suffix1400,suffix1440,suffix1464,suffix1480,suffix1520,suffix1536,suffix1560,suffix1600,suffix1632,suffix1640,suffix1656,suffix1680,suffix1720,suffix1728,suffix1752,suffix1760,suffix1800,suffix1824,suffix1840,suffix1848,suffix1880,suffix1920,suffix1944,suffix1960,suffix2000,suffix2016,suffix2040,suffix2080,suffix2112,suffix2120,suffix2136,suffix2160,suffix2200,suffix2208,suffix2232,suffix2240,suffix2260,suffix2300,suffix2304,suffix2328,suffix2340,suffix2380,suffix2400,suffix2420,suffix2424,suffix2460,suffix2496,suffix2500,suffix2520,suffix2540,suffix2580,suffix2592,suffix2616,suffix2620,suffix2660,suffix2688,suffix2700,suffix2712,suffix2740,suffix2780,suffix2784,suffix2808,suffix2820,suffix2847,suffix2880,suffix2887,suffix2904,suffix2927,suffix2967,suffix2976,suffix3000,suffix3007,suffix3047,suffix3072,suffix3087,suffix3096,suffix3127,suffix3167,suffix3168,bwAppend,List.append_nil,Partial.leave225Inv,bPart0,bPart1,bPart2,bPart3,bPart4,bPart5,bPart6,bPart7,bPart8,bPart9,bPart10,bPart11,bPart12,bPart13,bPart14,bPart15,bPart16,bPart17,bPart18,bPart19,bPart20,bPart21,bPart22,bPart23,bPart24,bPart25,bPart26,bPart27,bPart28,bPart29,bPart30,bPart31,bPart32,bPart33,List.append_assoc]
private theorem len0 : block0.length=24:=rfl
private theorem len24 : block24.length=16:=rfl
private theorem len40 : block40.length=40:=rfl
private theorem len80 : block80.length=16:=rfl
private theorem len96 : block96.length=24:=rfl
private theorem len120 : block120.length=40:=rfl
private theorem len160 : block160.length=32:=rfl
private theorem len192 : block192.length=8:=rfl
private theorem len200 : block200.length=16:=rfl
private theorem len216 : block216.length=24:=rfl
private theorem len240 : block240.length=40:=rfl
private theorem len280 : block280.length=8:=rfl
private theorem len288 : block288.length=24:=rfl
private theorem len312 : block312.length=8:=rfl
private theorem len320 : block320.length=40:=rfl
private theorem len360 : block360.length=24:=rfl
private theorem len384 : block384.length=16:=rfl
private theorem len400 : block400.length=8:=rfl
private theorem len408 : block408.length=32:=rfl
private theorem len440 : block440.length=40:=rfl
private theorem len480 : block480.length=24:=rfl
private theorem len504 : block504.length=16:=rfl
private theorem len520 : block520.length=40:=rfl
private theorem len560 : block560.length=16:=rfl
private theorem len576 : block576.length=24:=rfl
private theorem len600 : block600.length=40:=rfl
private theorem len640 : block640.length=32:=rfl
private theorem len672 : block672.length=8:=rfl
private theorem len680 : block680.length=16:=rfl
private theorem len696 : block696.length=24:=rfl
private theorem len720 : block720.length=40:=rfl
private theorem len760 : block760.length=8:=rfl
private theorem len768 : block768.length=24:=rfl
private theorem len792 : block792.length=8:=rfl
private theorem len800 : block800.length=40:=rfl
private theorem len840 : block840.length=24:=rfl
private theorem len864 : block864.length=16:=rfl
private theorem len880 : block880.length=8:=rfl
private theorem len888 : block888.length=32:=rfl
private theorem len920 : block920.length=40:=rfl
private theorem len960 : block960.length=24:=rfl
private theorem len984 : block984.length=16:=rfl
private theorem len1000 : block1000.length=40:=rfl
private theorem len1040 : block1040.length=16:=rfl
private theorem len1056 : block1056.length=24:=rfl
private theorem len1080 : block1080.length=40:=rfl
private theorem len1120 : block1120.length=32:=rfl
private theorem len1152 : block1152.length=8:=rfl
private theorem len1160 : block1160.length=16:=rfl
private theorem len1176 : block1176.length=24:=rfl
private theorem len1200 : block1200.length=40:=rfl
private theorem len1240 : block1240.length=8:=rfl
private theorem len1248 : block1248.length=24:=rfl
private theorem len1272 : block1272.length=8:=rfl
private theorem len1280 : block1280.length=40:=rfl
private theorem len1320 : block1320.length=24:=rfl
private theorem len1344 : block1344.length=16:=rfl
private theorem len1360 : block1360.length=8:=rfl
private theorem len1368 : block1368.length=32:=rfl
private theorem len1400 : block1400.length=40:=rfl
private theorem len1440 : block1440.length=24:=rfl
private theorem len1464 : block1464.length=16:=rfl
private theorem len1480 : block1480.length=40:=rfl
private theorem len1520 : block1520.length=16:=rfl
private theorem len1536 : block1536.length=24:=rfl
private theorem len1560 : block1560.length=40:=rfl
private theorem len1600 : block1600.length=32:=rfl
private theorem len1632 : block1632.length=8:=rfl
private theorem len1640 : block1640.length=16:=rfl
private theorem len1656 : block1656.length=24:=rfl
private theorem len1680 : block1680.length=40:=rfl
private theorem len1720 : block1720.length=8:=rfl
private theorem len1728 : block1728.length=24:=rfl
private theorem len1752 : block1752.length=8:=rfl
private theorem len1760 : block1760.length=40:=rfl
private theorem len1800 : block1800.length=24:=rfl
private theorem len1824 : block1824.length=16:=rfl
private theorem len1840 : block1840.length=8:=rfl
private theorem len1848 : block1848.length=32:=rfl
private theorem len1880 : block1880.length=40:=rfl
private theorem len1920 : block1920.length=24:=rfl
private theorem len1944 : block1944.length=16:=rfl
private theorem len1960 : block1960.length=40:=rfl
private theorem len2000 : block2000.length=16:=rfl
private theorem len2016 : block2016.length=24:=rfl
private theorem len2040 : block2040.length=40:=rfl
private theorem len2080 : block2080.length=32:=rfl
private theorem len2112 : block2112.length=8:=rfl
private theorem len2120 : block2120.length=16:=rfl
private theorem len2136 : block2136.length=24:=rfl
private theorem len2160 : block2160.length=40:=rfl
private theorem len2200 : block2200.length=8:=rfl
private theorem len2208 : block2208.length=24:=rfl
private theorem len2232 : block2232.length=8:=rfl
private theorem len2240 : block2240.length=20:=rfl
private theorem size0 : (GateMirror.forward group0).length=2260:=by
  simp only [GateMirror.forward,List.length_map,group0,suffix0,suffix24,suffix40,suffix80,suffix96,suffix120,suffix160,suffix192,suffix200,suffix216,suffix240,suffix280,suffix288,suffix312,suffix320,suffix360,suffix384,suffix400,suffix408,suffix440,suffix480,suffix504,suffix520,suffix560,suffix576,suffix600,suffix640,suffix672,suffix680,suffix696,suffix720,suffix760,suffix768,suffix792,suffix800,suffix840,suffix864,suffix880,suffix888,suffix920,suffix960,suffix984,suffix1000,suffix1040,suffix1056,suffix1080,suffix1120,suffix1152,suffix1160,suffix1176,suffix1200,suffix1240,suffix1248,suffix1272,suffix1280,suffix1320,suffix1344,suffix1360,suffix1368,suffix1400,suffix1440,suffix1464,suffix1480,suffix1520,suffix1536,suffix1560,suffix1600,suffix1632,suffix1640,suffix1656,suffix1680,suffix1720,suffix1728,suffix1752,suffix1760,suffix1800,suffix1824,suffix1840,suffix1848,suffix1880,suffix1920,suffix1944,suffix1960,suffix2000,suffix2016,suffix2040,suffix2080,suffix2112,suffix2120,suffix2136,suffix2160,suffix2200,suffix2208,suffix2232,suffix2240,len0,len24,len40,len80,len96,len120,len160,len192,len200,len216,len240,len280,len288,len312,len320,len360,len384,len400,len408,len440,len480,len504,len520,len560,len576,len600,len640,len672,len680,len696,len720,len760,len768,len792,len800,len840,len864,len880,len888,len920,len960,len984,len1000,len1040,len1056,len1080,len1120,len1152,len1160,len1176,len1200,len1240,len1248,len1272,len1280,len1320,len1344,len1360,len1368,len1400,len1440,len1464,len1480,len1520,len1536,len1560,len1600,len1632,len1640,len1656,len1680,len1720,len1728,len1752,len1760,len1800,len1824,len1840,len1848,len1880,len1920,len1944,len1960,len2000,len2016,len2040,len2080,len2112,len2120,len2136,len2160,len2200,len2208,len2232,len2240,List.length_append,List.length_nil]
private theorem len2260 : block2260.length=40:=rfl
private theorem len2300 : block2300.length=4:=rfl
private theorem len2304 : block2304.length=24:=rfl
private theorem len2328 : block2328.length=12:=rfl
private theorem len2340 : block2340.length=40:=rfl
private theorem len2380 : block2380.length=20:=rfl
private theorem len2400 : block2400.length=20:=rfl
private theorem len2420 : block2420.length=4:=rfl
private theorem len2424 : block2424.length=36:=rfl
private theorem len2460 : block2460.length=36:=rfl
private theorem len2496 : block2496.length=4:=rfl
private theorem len2500 : block2500.length=20:=rfl
private theorem len2520 : block2520.length=20:=rfl
private theorem len2540 : block2540.length=40:=rfl
private theorem len2580 : block2580.length=12:=rfl
private theorem len2592 : block2592.length=24:=rfl
private theorem len2616 : block2616.length=4:=rfl
private theorem len2620 : block2620.length=40:=rfl
private theorem len2660 : block2660.length=28:=rfl
private theorem len2688 : block2688.length=12:=rfl
private theorem len2700 : block2700.length=12:=rfl
private theorem len2712 : block2712.length=28:=rfl
private theorem len2740 : block2740.length=40:=rfl
private theorem len2780 : block2780.length=4:=rfl
private theorem len2784 : block2784.length=24:=rfl
private theorem len2808 : block2808.length=12:=rfl
private theorem len2820 : block2820.length=27:=rfl
private theorem size1 : (GateMirror.forward group1).length=587:=by
  simp only [GateMirror.forward,List.length_map,group1,suffix2260,suffix2300,suffix2304,suffix2328,suffix2340,suffix2380,suffix2400,suffix2420,suffix2424,suffix2460,suffix2496,suffix2500,suffix2520,suffix2540,suffix2580,suffix2592,suffix2616,suffix2620,suffix2660,suffix2688,suffix2700,suffix2712,suffix2740,suffix2780,suffix2784,suffix2808,suffix2820,len2260,len2300,len2304,len2328,len2340,len2380,len2400,len2420,len2424,len2460,len2496,len2500,len2520,len2540,len2580,len2592,len2616,len2620,len2660,len2688,len2700,len2712,len2740,len2780,len2784,len2808,len2820,List.length_append,List.length_nil]
private theorem pEq : GateMirror.forward group0 = Partial.leave225.take 2260 := by
  rw [←fEq,ops,fwAppend,←size0,List.take_left]
private theorem qEq : GateMirror.forward (group0++group1) = Partial.leave225.take 2847 := by
  have lengthEq:(GateMirror.forward (group0++group1)).length=2847:=by rw [fwAppend,List.length_append,size0,size1]
  rw [←fEq,ops,←List.append_assoc,fwAppend (group0++group1) group2,←lengthEq,List.take_left]
theorem inverts (s:State) (phase:∀m,(run Partial.leave225 m s).phase=s.phase)
    (initial:∀q, 1556≤q → q≤1717 → s.basis q=false)
    (core:zeros (run (Partial.leave225.take 2260) [] s) [1560,1576,1596,1613,1614])
    (post:(run (Partial.leave225.take 2847) [] s).basis 1556=false) (m n:List Bool):
    run Partial.leave225Inv n (run Partial.leave225 m s)=s:=by
  let s1:=run (GateMirror.forward group0) [] s
  let s2:=run (GateMirror.forward group1) [] s1
  have s2e:s2=run (GateMirror.forward (group0++group1)) [] s:=by
    simp [s2,s1,GateMirror.forward,List.map_append,run_append]
  have i0:Masked s (0x3fffffffffffffffffffffffeffffeffffe <<< 1556):=subMask (by decide +kernel) (fromRange (lo:=1556) (width:=162) (fun q h1 h2=>initial q h1 (Nat.le_of_lt_succ h2)))
  obtain ⟨h0,r0,z0⟩:=bit_sound group0 s _ _ cert0 i0
  have kc:zeros s1 [1560,1576,1596,1613,1614]:=by simpa only [s1,pEq] using core
  have i1:Masked s1 (0x1fffffffffffffffe0003fffffffff8 <<< 1556):=subMask (by decide +kernel) (bothMasks z0 (fromList kc))
  obtain ⟨h1,r1,z1⟩:=bit_sound group1 s1 _ _ cert1 i1
  have kp:zeros s2 [1556]:=by
    intro q hq
    obtain rfl: q=1556:=by simpa using hq
    rw [s2e,qEq];exact post
  have i2:Masked s2 (0x79 <<< 1556):=subMask (by decide +kernel) (bothMasks z1 (fromList kp))
  obtain ⟨h2,r2,z2⟩:=bit_sound group2 s2 _ _ cert2 i2
  have phys:∀g∈ops,proper g=true:=by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact h0 g h
    · rcases List.mem_append.mp h with h|h
      · exact h1 g h
      · exact h2 g h
  have ready:Ready s ops:=ready_append _ _ _ r0 (ready_append _ _ _ r1 r2)
  rw [←bEq,←fEq]
  exact invert ops s phys (all_prepared ops s phys (by rwa [fEq])) ready m n
end ECDSAAdd.Entrant.StairPacket.Leave225Mirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
private def block3024 : List Gate := [
  .x 1284,
  .make 1717 1284 1556,
  .x 1285,
  .make 1556 1285 1559,
  .x 1286,
  .make 1559 1286 1560,
  .x 1287,
  .make 1560 1287 1561,
  .x 1288,
  .make 1561 1288 1562,
  .cx 1562 1714,
  .pop 1561 1288 1562,
  .x 1288,
  .pop 1560 1287 1561,
  .x 1287,
  .pop 1559 1286 1560,
  .x 1286,
  .pop 1556 1285 1559,
  .x 1285,
  .pop 1717 1284 1556,
  .x 1284,
  .cx 949 934,
  .cx 934 949,
  .cx 949 934,
  .cx 950 935,
  .cx 935 950,
  .cx 950 935,
  .cx 951 936,
  .cx 936 951,
  .cx 951 936,
  .cx 952 937,
  .cx 937 952,
  .cx 952 937,
  .cx 953 938,
  .cx 938 953,
  .cx 953 938,
  .cx 954 939,
  .cx 939 954,
  .cx 954 939,
  .cx 955 940]
private def block3064 : List Gate := [
  .cx 940 955,
  .cx 955 940,
  .cx 956 941,
  .cx 941 956,
  .cx 956 941,
  .cx 957 942,
  .cx 942 957,
  .cx 957 942]
private def block3072 : List Gate := [
  .cx 958 943,
  .cx 943 958,
  .cx 958 943,
  .cx 959 944,
  .cx 944 959,
  .cx 959 944,
  .cx 960 945,
  .cx 945 960,
  .cx 960 945,
  .cx 961 946,
  .cx 946 961,
  .cx 961 946,
  .cx 962 947,
  .cx 947 962,
  .cx 962 947,
  .cx 963 948,
  .cx 948 963,
  .cx 963 948,
  .cx 964 949,
  .cx 949 964,
  .cx 964 949,
  .cx 965 950,
  .cx 950 965,
  .cx 965 950,
  .cx 966 951,
  .cx 951 966,
  .cx 966 951,
  .cx 967 952,
  .cx 952 967,
  .cx 967 952]
private def block3102 : List Gate := [
  .cx 968 953,
  .cx 953 968]
private def block3104 : List Gate := [
  .cx 968 953,
  .cx 969 954,
  .cx 954 969,
  .cx 969 954,
  .cx 970 955,
  .cx 955 970,
  .cx 970 955,
  .cx 971 956,
  .cx 956 971,
  .cx 971 956,
  .cx 972 957,
  .cx 957 972,
  .cx 972 957,
  .cx 973 958,
  .cx 958 973,
  .cx 973 958,
  .cx 974 959,
  .cx 959 974,
  .cx 974 959,
  .cx 975 960,
  .cx 960 975,
  .cx 975 960,
  .cx 976 961,
  .cx 961 976,
  .cx 976 961,
  .cx 977 962,
  .cx 962 977,
  .cx 977 962,
  .cx 978 963,
  .cx 963 978,
  .cx 978 963,
  .cx 979 964,
  .cx 964 979,
  .cx 979 964,
  .cx 980 965,
  .cx 965 980,
  .cx 980 965,
  .cx 981 966,
  .cx 966 981,
  .cx 981 966]
private def block3144 : List Gate := [
  .cx 982 967,
  .cx 967 982,
  .cx 982 967,
  .cx 983 968,
  .cx 968 983,
  .cx 983 968,
  .cx 984 969,
  .cx 969 984,
  .cx 984 969,
  .cx 985 970,
  .cx 970 985,
  .cx 985 970,
  .cx 986 971,
  .cx 971 986,
  .cx 986 971,
  .cx 987 972,
  .cx 972 987,
  .cx 987 972,
  .cx 988 973,
  .cx 973 988,
  .cx 988 973,
  .cx 989 974,
  .cx 974 989,
  .cx 989 974]
private def block3168 : List Gate := [
  .cx 990 975,
  .cx 975 990,
  .cx 990 975,
  .cx 991 976,
  .cx 976 991,
  .cx 991 976,
  .cx 992 977,
  .cx 977 992,
  .cx 992 977,
  .cx 993 978,
  .cx 978 993,
  .cx 993 978,
  .cx 994 979,
  .cx 979 994,
  .cx 994 979,
  .cx 995 980]
private def block3184 : List Gate := [
  .cx 980 995,
  .cx 995 980,
  .cx 996 981,
  .cx 981 996,
  .cx 996 981,
  .cx 997 982,
  .cx 982 997,
  .cx 997 982,
  .cx 998 983,
  .cx 983 998,
  .cx 998 983,
  .cx 999 984,
  .cx 984 999,
  .cx 999 984]
private def block3198 : List Gate := [
  .cx 1000 985,
  .cx 985 1000,
  .cx 1000 985,
  .cx 1001 986,
  .cx 986 1001,
  .cx 1001 986,
  .cx 1002 987,
  .cx 987 1002,
  .cx 1002 987,
  .cx 1003 988,
  .cx 988 1003,
  .cx 1003 988,
  .cx 1004 989,
  .cx 989 1004,
  .cx 1004 989,
  .cx 1005 990,
  .cx 990 1005,
  .cx 1005 990,
  .cx 1006 991,
  .cx 991 1006,
  .cx 1006 991,
  .cx 1007 992,
  .cx 992 1007,
  .cx 1007 992,
  .cx 1008 993,
  .cx 993 1008]
private def block3224 : List Gate := [
  .cx 1008 993,
  .cx 1009 994,
  .cx 994 1009,
  .cx 1009 994,
  .cx 1010 995,
  .cx 995 1010,
  .cx 1010 995,
  .cx 1011 996,
  .cx 996 1011,
  .cx 1011 996,
  .cx 1012 997,
  .cx 997 1012,
  .cx 1012 997,
  .cx 1013 998,
  .cx 998 1013,
  .cx 1013 998,
  .cx 1014 999,
  .cx 999 1014,
  .cx 1014 999,
  .cx 1015 1000,
  .cx 1000 1015,
  .cx 1015 1000,
  .cx 1016 1001,
  .cx 1001 1016,
  .cx 1016 1001,
  .cx 1017 1002,
  .cx 1002 1017,
  .cx 1017 1002,
  .cx 1018 1003,
  .cx 1003 1018,
  .cx 1018 1003,
  .cx 1019 1004,
  .cx 1004 1019,
  .cx 1019 1004,
  .cx 1020 1005,
  .cx 1005 1020,
  .cx 1020 1005,
  .cx 1021 1006,
  .cx 1006 1021,
  .cx 1021 1006]
private def block3264 : List Gate := [
  .cx 1022 1007,
  .cx 1007 1022,
  .cx 1022 1007,
  .cx 1023 1008,
  .cx 1008 1023,
  .cx 1023 1008,
  .cx 1024 1009,
  .cx 1009 1024,
  .cx 1024 1009,
  .cx 1025 1010,
  .cx 1010 1025,
  .cx 1025 1010,
  .cx 1026 1011,
  .cx 1011 1026,
  .cx 1026 1011,
  .cx 1027 1012,
  .cx 1012 1027,
  .cx 1027 1012,
  .cx 1028 1013,
  .cx 1013 1028,
  .cx 1028 1013,
  .cx 1029 1014,
  .cx 1014 1029,
  .cx 1029 1014,
  .cx 1030 1015,
  .cx 1015 1030,
  .cx 1030 1015,
  .cx 1031 1016,
  .cx 1016 1031,
  .cx 1031 1016]
private def block3294 : List Gate := [
  .cx 1032 1017,
  .cx 1017 1032,
  .cx 1032 1017,
  .cx 1033 1018,
  .cx 1018 1033,
  .cx 1033 1018,
  .cx 1034 1019,
  .cx 1019 1034,
  .cx 1034 1019,
  .cx 1035 1020]
private def block3304 : List Gate := [
  .cx 1020 1035,
  .cx 1035 1020,
  .cx 1036 1021,
  .cx 1021 1036,
  .cx 1036 1021,
  .cx 1037 1022,
  .cx 1022 1037,
  .cx 1037 1022,
  .cx 1038 1023,
  .cx 1023 1038,
  .cx 1038 1023,
  .cx 1039 1024,
  .cx 1024 1039,
  .cx 1039 1024,
  .cx 1040 1025,
  .cx 1025 1040,
  .cx 1040 1025,
  .cx 1041 1026,
  .cx 1026 1041,
  .cx 1041 1026,
  .cx 1042 1027,
  .cx 1027 1042,
  .cx 1042 1027,
  .cx 1598 1028,
  .cx 1028 1598,
  .cx 1598 1028,
  .cx 1599 1029,
  .cx 1029 1599,
  .cx 1599 1029,
  .cx 1600 1030,
  .cx 1030 1600,
  .cx 1600 1030,
  .cx 1601 1031,
  .cx 1031 1601,
  .cx 1601 1031,
  .cx 1602 1032,
  .cx 1032 1602,
  .cx 1602 1032,
  .cx 1603 1033,
  .cx 1033 1603]
private def block3344 : List Gate := [
  .cx 1603 1033,
  .cx 1604 1034,
  .cx 1034 1604,
  .cx 1604 1034,
  .cx 1605 1035,
  .cx 1035 1605,
  .cx 1605 1035,
  .cx 1606 1036,
  .cx 1036 1606,
  .cx 1606 1036,
  .cx 1607 1037,
  .cx 1037 1607,
  .cx 1607 1037,
  .cx 1608 1038,
  .cx 1038 1608,
  .cx 1608 1038]
private def block3360 : List Gate := [
  .cx 1609 1039,
  .cx 1039 1609,
  .cx 1609 1039,
  .cx 1610 1040,
  .cx 1040 1610,
  .cx 1610 1040,
  .cx 1611 1041,
  .cx 1041 1611,
  .cx 1611 1041,
  .cx 1612 1042,
  .cx 1042 1612,
  .cx 1612 1042,
  .cx 1557 1706,
  .cx 1706 1557,
  .cx 1557 1706,
  .cx 1558 1707,
  .cx 1707 1558,
  .cx 1558 1707,
  .cx 1715 1708,
  .cx 1708 1715,
  .cx 1715 1708,
  .cx 1713 1709,
  .cx 1709 1713,
  .cx 1713 1709]
private def block3384 : List Gate := [
  .cx 1717 1710,
  .cx 1710 1717,
  .cx 1717 1710,
  .cx 1716 1711,
  .cx 1711 1716,
  .cx 1716 1711]
private theorem check3384 : bitCheck block3384 0 = some 0 := by decide +kernel
private def suffix3384 := block3384 ++ ([]:List Gate)
private theorem valid3384 : bitCheck suffix3384 0 = some 0 := bit_join block3384 ([]:List Gate) _ 0 _ check3384 rfl
private theorem check3360 : bitCheck block3360 0 = some 0 := by decide +kernel
private def suffix3360 := block3360 ++ suffix3384
private theorem valid3360 : bitCheck suffix3360 0 = some 0 := bit_join block3360 suffix3384 _ 0 _ check3360 valid3384
private theorem check3344 : bitCheck block3344 0 = some 0 := by decide +kernel
private def suffix3344 := block3344 ++ suffix3360
private theorem valid3344 : bitCheck suffix3344 0 = some 0 := bit_join block3344 suffix3360 _ 0 _ check3344 valid3360
private theorem check3304 : bitCheck block3304 0 = some 0 := by decide +kernel
private def suffix3304 := block3304 ++ suffix3344
private theorem valid3304 : bitCheck suffix3304 0 = some 0 := bit_join block3304 suffix3344 _ 0 _ check3304 valid3344
private theorem check3294 : bitCheck block3294 0 = some 0 := by decide +kernel
private def suffix3294 := block3294 ++ suffix3304
private theorem valid3294 : bitCheck suffix3294 0 = some 0 := bit_join block3294 suffix3304 _ 0 _ check3294 valid3304
private theorem check3264 : bitCheck block3264 0 = some 0 := by decide +kernel
private def suffix3264 := block3264 ++ suffix3294
private theorem valid3264 : bitCheck suffix3264 0 = some 0 := bit_join block3264 suffix3294 _ 0 _ check3264 valid3294
private theorem check3224 : bitCheck block3224 0 = some 0 := by decide +kernel
private def suffix3224 := block3224 ++ suffix3264
private theorem valid3224 : bitCheck suffix3224 0 = some 0 := bit_join block3224 suffix3264 _ 0 _ check3224 valid3264
private theorem check3198 : bitCheck block3198 0 = some 0 := by decide +kernel
private def suffix3198 := block3198 ++ suffix3224
private theorem valid3198 : bitCheck suffix3198 0 = some 0 := bit_join block3198 suffix3224 _ 0 _ check3198 valid3224
private theorem check3184 : bitCheck block3184 0 = some 0 := by decide +kernel
private def suffix3184 := block3184 ++ suffix3198
private theorem valid3184 : bitCheck suffix3184 0 = some 0 := bit_join block3184 suffix3198 _ 0 _ check3184 valid3198
private theorem check3168 : bitCheck block3168 0 = some 0 := by decide +kernel
private def suffix3168 := block3168 ++ suffix3184
private theorem valid3168 : bitCheck suffix3168 0 = some 0 := bit_join block3168 suffix3184 _ 0 _ check3168 valid3184
private theorem check3144 : bitCheck block3144 0 = some 0 := by decide +kernel
private def suffix3144 := block3144 ++ suffix3168
private theorem valid3144 : bitCheck suffix3144 0 = some 0 := bit_join block3144 suffix3168 _ 0 _ check3144 valid3168
private theorem check3104 : bitCheck block3104 0 = some 0 := by decide +kernel
private def suffix3104 := block3104 ++ suffix3144
private theorem valid3104 : bitCheck suffix3104 0 = some 0 := bit_join block3104 suffix3144 _ 0 _ check3104 valid3144
private theorem check3102 : bitCheck block3102 0 = some 0 := by decide +kernel
private def suffix3102 := block3102 ++ suffix3104
private theorem valid3102 : bitCheck suffix3102 0 = some 0 := bit_join block3102 suffix3104 _ 0 _ check3102 valid3104
private theorem check3072 : bitCheck block3072 0 = some 0 := by decide +kernel
private def suffix3072 := block3072 ++ suffix3102
private theorem valid3072 : bitCheck suffix3072 0 = some 0 := bit_join block3072 suffix3102 _ 0 _ check3072 valid3102
private theorem check3064 : bitCheck block3064 0 = some 0 := by decide +kernel
private def suffix3064 := block3064 ++ suffix3072
private theorem valid3064 : bitCheck suffix3064 0 = some 0 := bit_join block3064 suffix3072 _ 0 _ check3064 valid3072
private theorem check3024 : bitCheck block3024 0 = some (0x79 <<< 1556) := by decide +kernel
private def suffix3024 := block3024 ++ suffix3064
private theorem valid3024 : bitCheck suffix3024 0 = some (0x79 <<< 1556) := bit_join block3024 suffix3064 _ 0 _ check3024 valid3064
private def group2 := suffix3024
private theorem cert2 : bitCheck group2 0 = some (0x79 <<< 1556) := valid3024
private def block2395 : List Gate := [
  .ccx 1556 408 923,
  .ccx 1556 409 924,
  .ccx 1556 410 925,
  .ccx 1556 411 926,
  .ccx 1556 412 927]
private def block2400 : List Gate := [
  .ccx 1556 413 928,
  .ccx 1556 414 929,
  .ccx 1556 415 930,
  .ccx 1556 416 931,
  .ccx 1556 417 932,
  .ccx 1556 418 933,
  .x 923,
  .x 924,
  .x 925,
  .x 926,
  .x 927,
  .x 928,
  .x 929,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .make 923 1558 1559,
  .make 924 1559 1560,
  .make 925 1560 1561,
  .make 926 1561 1562,
  .make 927 1562 1563,
  .make 928 1563 1564,
  .make 929 1564 1565,
  .make 930 1565 1566,
  .make 931 1566 1567,
  .make 932 1567 1568,
  .cx 1568 933,
  .pop 932 1567 1568,
  .cx 1567 932]
private def block2430 : List Gate := [
  .pop 931 1566 1567,
  .cx 1566 931,
  .pop 930 1565 1566,
  .cx 1565 930,
  .pop 929 1564 1565]
private def block2435 : List Gate := [
  .cx 1564 929,
  .pop 928 1563 1564,
  .cx 1563 928,
  .pop 927 1562 1563,
  .cx 1562 927,
  .pop 926 1561 1562,
  .cx 1561 926,
  .pop 925 1560 1561,
  .cx 1560 925,
  .pop 924 1559 1560,
  .cx 1559 924,
  .pop 923 1558 1559,
  .cx 1558 923,
  .x 923,
  .x 924,
  .x 925,
  .x 926,
  .x 927,
  .x 928,
  .x 929,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .pop 922 1557 1558,
  .cx 407 1557,
  .x 1557,
  .make 416 417 1558,
  .x 1558,
  .x 418,
  .x 949,
  .x 950,
  .x 951,
  .x 952,
  .x 953,
  .x 954,
  .x 955,
  .x 956,
  .x 957,
  .x 958]
private def block2475 : List Gate := [
  .x 959,
  .x 960,
  .x 961,
  .x 962,
  .x 963,
  .x 964,
  .x 965,
  .x 966,
  .x 967,
  .x 968,
  .x 969,
  .x 970,
  .x 971,
  .x 972,
  .x 973,
  .x 974,
  .x 975,
  .x 976,
  .x 977,
  .x 978,
  .x 979]
private def block2496 : List Gate := [
  .x 980,
  .x 981,
  .x 982,
  .x 983,
  .x 984,
  .x 985,
  .x 986,
  .x 987,
  .x 988,
  .x 989,
  .x 990,
  .x 991,
  .x 992,
  .x 993,
  .x 994,
  .x 995,
  .x 996,
  .x 997,
  .x 998]
private def block2515 : List Gate := [
  .x 999,
  .x 1000,
  .x 1001,
  .x 1002,
  .x 1003,
  .x 1004,
  .x 1005,
  .x 1006,
  .x 1007,
  .x 1008,
  .x 1009]
private def block2526 : List Gate := [
  .x 1010,
  .x 1011,
  .x 1012,
  .x 1013,
  .x 1014,
  .x 1015,
  .x 1016,
  .x 1017,
  .x 1018,
  .x 1019,
  .x 1020,
  .x 1021,
  .x 1022,
  .x 1023,
  .x 1024,
  .x 1025,
  .x 1026,
  .x 1027,
  .x 1028,
  .x 1029,
  .x 1030,
  .x 1031,
  .x 1032,
  .x 1033,
  .x 1034,
  .x 1035,
  .x 1036,
  .x 1037,
  .x 1038]
private def block2555 : List Gate := [
  .x 1039,
  .x 1040,
  .x 1041,
  .x 1042,
  .x 1598,
  .x 1599,
  .x 1600,
  .x 1601,
  .x 1602,
  .x 1603,
  .x 1604,
  .x 1605,
  .x 1606,
  .x 1607,
  .x 1608,
  .x 1609,
  .x 1610,
  .x 1611,
  .x 1612,
  .make 1558 418 1559,
  .make 1559 949 1560,
  .make 1560 950 1561,
  .make 1561 951 1562,
  .make 1562 952 1563,
  .make 1563 953 1564,
  .make 1564 954 1565,
  .make 1565 955 1566,
  .make 1566 956 1567,
  .make 1567 957 1568,
  .make 1568 958 1569,
  .make 1569 959 1570,
  .make 1570 960 1571,
  .make 1571 961 1572,
  .make 1572 962 1573,
  .make 1573 963 1574,
  .make 1574 964 1575,
  .make 1575 965 1576]
private def block2592 : List Gate := [
  .make 1576 966 1577,
  .make 1577 967 1578,
  .make 1578 968 1579]
private def block2595 : List Gate := [
  .make 1579 969 1580,
  .make 1580 970 1581,
  .make 1581 971 1582,
  .make 1582 972 1583,
  .make 1583 973 1584,
  .make 1584 974 1585,
  .make 1585 975 1586,
  .make 1586 976 1587,
  .make 1587 977 1588,
  .make 1588 978 1589,
  .make 1589 979 1590,
  .make 1590 980 1591,
  .make 1591 981 1592,
  .make 1592 982 1593,
  .make 1593 983 1594,
  .make 1594 984 1595,
  .make 1595 985 1596,
  .make 1596 986 1597,
  .make 1597 987 1613,
  .make 1613 988 1614,
  .make 1614 989 1615,
  .make 1615 990 1616,
  .make 1616 991 1617,
  .make 1617 992 1618,
  .make 1618 993 1619,
  .make 1619 994 1620,
  .make 1620 995 1621]
private def block2622 : List Gate := [
  .make 1621 996 1622,
  .make 1622 997 1623,
  .make 1623 998 1624,
  .make 1624 999 1625,
  .make 1625 1000 1626,
  .make 1626 1001 1627,
  .make 1627 1002 1628,
  .make 1628 1003 1629,
  .make 1629 1004 1630,
  .make 1630 1005 1631,
  .make 1631 1006 1632,
  .make 1632 1007 1633,
  .make 1633 1008 1634]
private def block2635 : List Gate := [
  .make 1634 1009 1635,
  .make 1635 1010 1636,
  .make 1636 1011 1637,
  .make 1637 1012 1638,
  .make 1638 1013 1639,
  .make 1639 1014 1640,
  .make 1640 1015 1641,
  .make 1641 1016 1642,
  .make 1642 1017 1643,
  .make 1643 1018 1644,
  .make 1644 1019 1645,
  .make 1645 1020 1646,
  .make 1646 1021 1647,
  .make 1647 1022 1648,
  .make 1648 1023 1649,
  .make 1649 1024 1650,
  .make 1650 1025 1651,
  .make 1651 1026 1652,
  .make 1652 1027 1653,
  .make 1653 1028 1654,
  .make 1654 1029 1655,
  .make 1655 1030 1656,
  .make 1656 1031 1657,
  .make 1657 1032 1658,
  .make 1658 1033 1659,
  .make 1659 1034 1660,
  .make 1660 1035 1661,
  .make 1661 1036 1662,
  .make 1662 1037 1663,
  .make 1663 1038 1664,
  .make 1664 1039 1665,
  .make 1665 1040 1666,
  .make 1666 1041 1667,
  .make 1667 1042 1668,
  .make 1668 1598 1669,
  .make 1669 1599 1670,
  .make 1670 1600 1671,
  .make 1671 1601 1672,
  .make 1672 1602 1673,
  .make 1673 1603 1674]
private def block2675 : List Gate := [
  .make 1674 1604 1675,
  .make 1675 1605 1676,
  .make 1676 1606 1677,
  .make 1677 1607 1678,
  .make 1678 1608 1679,
  .make 1679 1609 1680,
  .make 1680 1610 1681,
  .make 1681 1611 1682,
  .make 1682 1612 1683,
  .cx 1683 1557,
  .x 1557,
  .pop 1682 1612 1683,
  .pop 1681 1611 1682]
private def block2688 : List Gate := [
  .pop 1680 1610 1681,
  .pop 1679 1609 1680,
  .pop 1678 1608 1679,
  .pop 1677 1607 1678,
  .pop 1676 1606 1677,
  .pop 1675 1605 1676,
  .pop 1674 1604 1675,
  .pop 1673 1603 1674,
  .pop 1672 1602 1673,
  .pop 1671 1601 1672,
  .pop 1670 1600 1671,
  .pop 1669 1599 1670,
  .pop 1668 1598 1669,
  .pop 1667 1042 1668,
  .pop 1666 1041 1667,
  .pop 1665 1040 1666,
  .pop 1664 1039 1665,
  .pop 1663 1038 1664,
  .pop 1662 1037 1663,
  .pop 1661 1036 1662,
  .pop 1660 1035 1661,
  .pop 1659 1034 1660,
  .pop 1658 1033 1659,
  .pop 1657 1032 1658,
  .pop 1656 1031 1657,
  .pop 1655 1030 1656,
  .pop 1654 1029 1655]
private def block2715 : List Gate := [
  .pop 1653 1028 1654,
  .pop 1652 1027 1653,
  .pop 1651 1026 1652]
private def block2718 : List Gate := [
  .pop 1650 1025 1651,
  .pop 1649 1024 1650,
  .pop 1648 1023 1649,
  .pop 1647 1022 1648,
  .pop 1646 1021 1647,
  .pop 1645 1020 1646,
  .pop 1644 1019 1645,
  .pop 1643 1018 1644,
  .pop 1642 1017 1643,
  .pop 1641 1016 1642,
  .pop 1640 1015 1641,
  .pop 1639 1014 1640,
  .pop 1638 1013 1639,
  .pop 1637 1012 1638,
  .pop 1636 1011 1637,
  .pop 1635 1010 1636,
  .pop 1634 1009 1635,
  .pop 1633 1008 1634,
  .pop 1632 1007 1633,
  .pop 1631 1006 1632,
  .pop 1630 1005 1631,
  .pop 1629 1004 1630,
  .pop 1628 1003 1629,
  .pop 1627 1002 1628,
  .pop 1626 1001 1627,
  .pop 1625 1000 1626,
  .pop 1624 999 1625,
  .pop 1623 998 1624,
  .pop 1622 997 1623,
  .pop 1621 996 1622,
  .pop 1620 995 1621,
  .pop 1619 994 1620,
  .pop 1618 993 1619,
  .pop 1617 992 1618,
  .pop 1616 991 1617,
  .pop 1615 990 1616,
  .pop 1614 989 1615]
private def block2755 : List Gate := [
  .pop 1613 988 1614,
  .pop 1597 987 1613,
  .pop 1596 986 1597,
  .pop 1595 985 1596,
  .pop 1594 984 1595,
  .pop 1593 983 1594,
  .pop 1592 982 1593,
  .pop 1591 981 1592,
  .pop 1590 980 1591,
  .pop 1589 979 1590,
  .pop 1588 978 1589,
  .pop 1587 977 1588,
  .pop 1586 976 1587,
  .pop 1585 975 1586,
  .pop 1584 974 1585,
  .pop 1583 973 1584,
  .pop 1582 972 1583,
  .pop 1581 971 1582,
  .pop 1580 970 1581,
  .pop 1579 969 1580,
  .pop 1578 968 1579,
  .pop 1577 967 1578,
  .pop 1576 966 1577,
  .pop 1575 965 1576,
  .pop 1574 964 1575,
  .pop 1573 963 1574,
  .pop 1572 962 1573,
  .pop 1571 961 1572,
  .pop 1570 960 1571]
private def block2784 : List Gate := [
  .pop 1569 959 1570,
  .pop 1568 958 1569,
  .pop 1567 957 1568,
  .pop 1566 956 1567,
  .pop 1565 955 1566,
  .pop 1564 954 1565,
  .pop 1563 953 1564,
  .pop 1562 952 1563,
  .pop 1561 951 1562,
  .pop 1560 950 1561,
  .pop 1559 949 1560]
private def block2795 : List Gate := [
  .pop 1558 418 1559,
  .x 1612,
  .x 1611,
  .x 1610,
  .x 1609,
  .x 1608,
  .x 1607,
  .x 1606,
  .x 1605,
  .x 1604,
  .x 1603,
  .x 1602,
  .x 1601,
  .x 1600,
  .x 1599,
  .x 1598,
  .x 1042,
  .x 1041,
  .x 1040]
private def block2814 : List Gate := [
  .x 1039,
  .x 1038,
  .x 1037,
  .x 1036,
  .x 1035,
  .x 1034,
  .x 1033,
  .x 1032,
  .x 1031,
  .x 1030,
  .x 1029,
  .x 1028,
  .x 1027,
  .x 1026,
  .x 1025,
  .x 1024,
  .x 1023,
  .x 1022,
  .x 1021,
  .x 1020,
  .x 1019]
private def block2835 : List Gate := [
  .x 1018,
  .x 1017,
  .x 1016,
  .x 1015,
  .x 1014,
  .x 1013,
  .x 1012,
  .x 1011,
  .x 1010,
  .x 1009,
  .x 1008,
  .x 1007,
  .x 1006,
  .x 1005,
  .x 1004,
  .x 1003,
  .x 1002,
  .x 1001,
  .x 1000,
  .x 999,
  .x 998,
  .x 997,
  .x 996,
  .x 995,
  .x 994,
  .x 993,
  .x 992,
  .x 991,
  .x 990,
  .x 989,
  .x 988,
  .x 987,
  .x 986,
  .x 985,
  .x 984,
  .x 983,
  .x 982,
  .x 981,
  .x 980,
  .x 979]
private def block2875 : List Gate := [
  .x 978,
  .x 977,
  .x 976,
  .x 975,
  .x 974]
private def block2880 : List Gate := [
  .x 973,
  .x 972,
  .x 971,
  .x 970,
  .x 969,
  .x 968,
  .x 967,
  .x 966,
  .x 965,
  .x 964,
  .x 963,
  .x 962,
  .x 961,
  .x 960,
  .x 959,
  .x 958,
  .x 957,
  .x 956,
  .x 955,
  .x 954,
  .x 953,
  .x 952,
  .x 951,
  .x 950,
  .x 949,
  .x 418,
  .x 1558,
  .pop 416 417 1558,
  .make 1556 1557 1558,
  .x 1558]
private def block2910 : List Gate := [
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .x 926]
private def block2915 : List Gate := [
  .x 927,
  .x 928,
  .x 929,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .make 1558 922 1559,
  .make 1559 923 1560,
  .make 1560 924 1561,
  .make 1561 925 1562,
  .make 1562 926 1563,
  .make 1563 927 1564,
  .make 1564 928 1565,
  .make 1565 929 1566,
  .make 1566 930 1567,
  .make 1567 931 1568,
  .make 1568 932 1569,
  .make 1569 933 1570,
  .cx 1570 1556,
  .x 1556,
  .pop 1569 933 1570,
  .pop 1568 932 1569,
  .pop 1567 931 1568,
  .pop 1566 930 1567,
  .pop 1565 929 1566,
  .pop 1564 928 1565,
  .pop 1563 927 1564,
  .pop 1562 926 1563,
  .pop 1561 925 1562,
  .pop 1560 924 1561,
  .pop 1559 923 1560,
  .pop 1558 922 1559,
  .x 933,
  .x 932,
  .x 931,
  .x 930,
  .x 929,
  .x 928,
  .x 927]
private def block2955 : List Gate := [
  .x 926,
  .x 925,
  .x 924,
  .x 923,
  .x 922,
  .x 1558,
  .x 256,
  .x 257,
  .x 258,
  .x 259,
  .x 260,
  .x 261,
  .x 262,
  .x 263,
  .x 264,
  .x 265,
  .x 266,
  .x 267,
  .x 268,
  .x 269,
  .x 270]
private def block2976 : List Gate := [
  .cx 1715 922,
  .cx 1715 923,
  .cx 1715 924,
  .cx 1715 925,
  .cx 1715 926,
  .cx 1715 927,
  .cx 1715 928,
  .cx 1715 929,
  .cx 1715 930,
  .cx 1715 931,
  .cx 1715 932,
  .cx 1715 933,
  .cx 407 922,
  .ccx 270 922 407,
  .cx 407 922,
  .cx 408 923,
  .ccx 270 923 408,
  .cx 408 923,
  .cx 409 924]
private def block2995 : List Gate := [
  .ccx 270 924 409,
  .cx 409 924,
  .cx 410 925,
  .ccx 270 925 410,
  .cx 410 925,
  .cx 411 926,
  .ccx 270 926 411,
  .cx 411 926,
  .cx 412 927,
  .ccx 270 927 412,
  .cx 412 927]
private def block3006 : List Gate := [
  .cx 413 928,
  .ccx 270 928 413,
  .cx 413 928,
  .cx 414 929,
  .ccx 270 929 414,
  .cx 414 929,
  .cx 415 930,
  .ccx 270 930 415,
  .cx 415 930,
  .cx 416 931,
  .ccx 270 931 416,
  .cx 416 931,
  .cx 417 932,
  .ccx 270 932 417,
  .cx 417 932,
  .cx 418 933,
  .ccx 270 933 418,
  .cx 418 933]
private theorem check3006 : bitCheck block3006 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix3006 := block3006 ++ ([]:List Gate)
private theorem valid3006 : bitCheck suffix3006 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block3006 ([]:List Gate) _ (0x78 <<< 1556) _ check3006 rfl
private theorem check2995 : bitCheck block2995 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2995 := block2995 ++ suffix3006
private theorem valid2995 : bitCheck suffix2995 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2995 suffix3006 _ (0x78 <<< 1556) _ check2995 valid3006
private theorem check2976 : bitCheck block2976 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2976 := block2976 ++ suffix2995
private theorem valid2976 : bitCheck suffix2976 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2976 suffix2995 _ (0x78 <<< 1556) _ check2976 valid2995
private theorem check2955 : bitCheck block2955 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix2955 := block2955 ++ suffix2976
private theorem valid2955 : bitCheck suffix2955 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block2955 suffix2976 _ (0x78 <<< 1556) _ check2955 valid2976
private theorem check2915 : bitCheck block2915 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2915 := block2915 ++ suffix2955
private theorem valid2915 : bitCheck suffix2915 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2915 suffix2955 _ (0x78 <<< 1556) _ check2915 valid2955
private theorem check2910 : bitCheck block2910 (0x7ff8 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2910 := block2910 ++ suffix2915
private theorem valid2910 : bitCheck suffix2910 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2910 suffix2915 _ (0x7ff8 <<< 1556) _ check2910 valid2915
private theorem check2880 : bitCheck block2880 (0x7ff8 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2880 := block2880 ++ suffix2910
private theorem valid2880 : bitCheck suffix2880 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2880 suffix2910 _ (0x7ff8 <<< 1556) _ check2880 valid2910
private theorem check2875 : bitCheck block2875 (0x7ff8 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2875 := block2875 ++ suffix2880
private theorem valid2875 : bitCheck suffix2875 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2875 suffix2880 _ (0x7ff8 <<< 1556) _ check2875 valid2880
private theorem check2835 : bitCheck block2835 (0x7ff8 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2835 := block2835 ++ suffix2875
private theorem valid2835 : bitCheck suffix2835 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2835 suffix2875 _ (0x7ff8 <<< 1556) _ check2835 valid2875
private theorem check2814 : bitCheck block2814 (0x7ff8 <<< 1556) = some (0x7ff8 <<< 1556) := by decide +kernel
private def suffix2814 := block2814 ++ suffix2835
private theorem valid2814 : bitCheck suffix2814 (0x78 <<< 1556) = some (0x7ff8 <<< 1556) := bit_join block2814 suffix2835 _ (0x7ff8 <<< 1556) _ check2814 valid2835
private theorem check2795 : bitCheck block2795 (0x7ff8 <<< 1556) = some (0x7ff0 <<< 1556) := by decide +kernel
private def suffix2795 := block2795 ++ suffix2814
private theorem valid2795 : bitCheck suffix2795 (0x78 <<< 1556) = some (0x7ff0 <<< 1556) := bit_join block2795 suffix2814 _ (0x7ff8 <<< 1556) _ check2795 valid2814
private theorem check2784 : bitCheck block2784 (0x7ff0 <<< 1556) = some 0 := by decide +kernel
private def suffix2784 := block2784 ++ suffix2795
private theorem valid2784 : bitCheck suffix2784 (0x78 <<< 1556) = some 0 := bit_join block2784 suffix2795 _ (0x7ff0 <<< 1556) _ check2784 valid2795
private theorem check2755 : bitCheck block2755 0 = some 0 := by decide +kernel
private def suffix2755 := block2755 ++ suffix2784
private theorem valid2755 : bitCheck suffix2755 (0x78 <<< 1556) = some 0 := bit_join block2755 suffix2784 _ 0 _ check2755 valid2784
private theorem check2718 : bitCheck block2718 0 = some 0 := by decide +kernel
private def suffix2718 := block2718 ++ suffix2755
private theorem valid2718 : bitCheck suffix2718 (0x78 <<< 1556) = some 0 := bit_join block2718 suffix2755 _ 0 _ check2718 valid2755
private theorem check2715 : bitCheck block2715 0 = some 0 := by decide +kernel
private def suffix2715 := block2715 ++ suffix2718
private theorem valid2715 : bitCheck suffix2715 (0x78 <<< 1556) = some 0 := bit_join block2715 suffix2718 _ 0 _ check2715 valid2718
private theorem check2688 : bitCheck block2688 0 = some 0 := by decide +kernel
private def suffix2688 := block2688 ++ suffix2715
private theorem valid2688 : bitCheck suffix2688 (0x78 <<< 1556) = some 0 := bit_join block2688 suffix2715 _ 0 _ check2688 valid2715
private theorem check2675 : bitCheck block2675 0 = some (0xff800000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2675 := block2675 ++ suffix2688
private theorem valid2675 : bitCheck suffix2675 (0x78 <<< 1556) = some (0xff800000000000000000000000000000 <<< 1556) := bit_join block2675 suffix2688 _ 0 _ check2675 valid2688
private theorem check2635 : bitCheck block2635 (0xff800000000000000000000000000000 <<< 1556) = some (0xffffffffffff80000000000000000000 <<< 1556) := by decide +kernel
private def suffix2635 := block2635 ++ suffix2675
private theorem valid2635 : bitCheck suffix2635 (0x78 <<< 1556) = some (0xffffffffffff80000000000000000000 <<< 1556) := bit_join block2635 suffix2675 _ (0xff800000000000000000000000000000 <<< 1556) _ check2635 valid2675
private theorem check2622 : bitCheck block2622 (0xffffffffffff80000000000000000000 <<< 1556) = some (0xfffffffffffffffc0000000000000000 <<< 1556) := by decide +kernel
private def suffix2622 := block2622 ++ suffix2635
private theorem valid2622 : bitCheck suffix2622 (0x78 <<< 1556) = some (0xfffffffffffffffc0000000000000000 <<< 1556) := bit_join block2622 suffix2635 _ (0xffffffffffff80000000000000000000 <<< 1556) _ check2622 valid2635
private theorem check2595 : bitCheck block2595 (0xfffffffffffffffc0000000000000000 <<< 1556) = some (0xfffffffffffffffffe0003ffff000000 <<< 1556) := by decide +kernel
private def suffix2595 := block2595 ++ suffix2622
private theorem valid2595 : bitCheck suffix2595 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003ffff000000 <<< 1556) := bit_join block2595 suffix2622 _ (0xfffffffffffffffc0000000000000000 <<< 1556) _ check2595 valid2622
private theorem check2592 : bitCheck block2592 (0xfffffffffffffffffe0003ffff000000 <<< 1556) = some (0xfffffffffffffffffe0003ffffe00000 <<< 1556) := by decide +kernel
private def suffix2592 := block2592 ++ suffix2595
private theorem valid2592 : bitCheck suffix2592 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003ffffe00000 <<< 1556) := bit_join block2592 suffix2595 _ (0xfffffffffffffffffe0003ffff000000 <<< 1556) _ check2592 valid2595
private theorem check2555 : bitCheck block2555 (0xfffffffffffffffffe0003ffffe00000 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2555 := block2555 ++ suffix2592
private theorem valid2555 : bitCheck suffix2555 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2555 suffix2592 _ (0xfffffffffffffffffe0003ffffe00000 <<< 1556) _ check2555 valid2592
private theorem check2526 : bitCheck block2526 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2526 := block2526 ++ suffix2555
private theorem valid2526 : bitCheck suffix2526 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2526 suffix2555 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2526 valid2555
private theorem check2515 : bitCheck block2515 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2515 := block2515 ++ suffix2526
private theorem valid2515 : bitCheck suffix2515 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2515 suffix2526 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2515 valid2526
private theorem check2496 : bitCheck block2496 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2496 := block2496 ++ suffix2515
private theorem valid2496 : bitCheck suffix2496 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2496 suffix2515 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2496 valid2515
private theorem check2475 : bitCheck block2475 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2475 := block2475 ++ suffix2496
private theorem valid2475 : bitCheck suffix2475 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2475 suffix2496 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2475 valid2496
private theorem check2435 : bitCheck block2435 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffe00 <<< 1556) := by decide +kernel
private def suffix2435 := block2435 ++ suffix2475
private theorem valid2435 : bitCheck suffix2435 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffe00 <<< 1556) := bit_join block2435 suffix2475 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2435 valid2475
private theorem check2430 : bitCheck block2430 (0xfffffffffffffffffe0003fffffffe00 <<< 1556) = some (0xfffffffffffffffffe0003fffffff000 <<< 1556) := by decide +kernel
private def suffix2430 := block2430 ++ suffix2435
private theorem valid2430 : bitCheck suffix2430 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffff000 <<< 1556) := bit_join block2430 suffix2435 _ (0xfffffffffffffffffe0003fffffffe00 <<< 1556) _ check2430 valid2435
private theorem check2400 : bitCheck block2400 (0xfffffffffffffffffe0003fffffff000 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2400 := block2400 ++ suffix2430
private theorem valid2400 : bitCheck suffix2400 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2400 suffix2430 _ (0xfffffffffffffffffe0003fffffff000 <<< 1556) _ check2400 valid2430
private theorem check2395 : bitCheck block2395 (0xfffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2395 := block2395 ++ suffix2400
private theorem valid2395 : bitCheck suffix2395 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2395 suffix2400 _ (0xfffffffffffffffffe0003fffffffff8 <<< 1556) _ check2395 valid2400
private def group1 := suffix2395
private theorem cert1 : bitCheck group1 (0x78 <<< 1556) = some (0xfffffffffffffffffe0003fffffffff8 <<< 1556) := valid2395
private def block0 : List Gate := [
  .cx 425 1715,
  .cx 940 1715,
  .cx 407 922,
  .ccx 270 922 407,
  .cx 407 922,
  .cx 408 923,
  .ccx 270 923 408,
  .cx 408 923,
  .cx 409 924,
  .ccx 270 924 409,
  .cx 409 924,
  .cx 410 925,
  .ccx 270 925 410,
  .cx 410 925,
  .cx 411 926,
  .ccx 270 926 411,
  .cx 411 926,
  .cx 412 927,
  .ccx 270 927 412,
  .cx 412 927,
  .cx 413 928,
  .ccx 270 928 413,
  .cx 413 928,
  .cx 414 929,
  .ccx 270 929 414,
  .cx 414 929,
  .cx 415 930,
  .ccx 270 930 415,
  .cx 415 930,
  .cx 416 931]
private def block30 : List Gate := [
  .ccx 270 931 416,
  .cx 416 931,
  .cx 417 932,
  .ccx 270 932 417,
  .cx 417 932,
  .cx 418 933,
  .ccx 270 933 418,
  .cx 418 933,
  .cx 419 934,
  .ccx 270 934 419]
private def block40 : List Gate := [
  .cx 419 934,
  .cx 420 935,
  .ccx 270 935 420,
  .cx 420 935,
  .cx 421 936,
  .ccx 270 936 421,
  .cx 421 936,
  .cx 422 937,
  .ccx 270 937 422,
  .cx 422 937,
  .cx 423 938,
  .ccx 270 938 423,
  .cx 423 938,
  .cx 424 939,
  .ccx 270 939 424,
  .cx 424 939,
  .cx 425 940,
  .ccx 270 940 425,
  .cx 425 940,
  .cx 1715 922,
  .cx 1715 923,
  .cx 1715 924,
  .cx 1715 925,
  .cx 1715 926,
  .cx 1715 927,
  .cx 1715 928,
  .cx 1715 929,
  .cx 1715 930,
  .cx 1715 931,
  .cx 1715 932,
  .cx 1715 933,
  .cx 1715 934,
  .cx 1715 935,
  .cx 1715 936,
  .cx 1715 937,
  .cx 1715 938,
  .cx 1715 939,
  .cx 1715 940,
  .x 256,
  .x 257]
private def block80 : List Gate := [
  .x 258,
  .x 259,
  .x 260,
  .x 261,
  .x 262,
  .x 263,
  .x 264,
  .x 265,
  .x 266,
  .x 267,
  .x 268,
  .x 269,
  .x 270,
  .x 922,
  .x 923,
  .x 924]
private def block96 : List Gate := [
  .x 925,
  .x 926,
  .x 927,
  .x 928,
  .x 929,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .x 934,
  .x 935,
  .x 936,
  .x 937,
  .x 938,
  .x 939,
  .x 940,
  .make 922 923 1557,
  .make 1557 924 1558,
  .make 1558 925 1559,
  .make 1559 926 1560,
  .make 1560 927 1561,
  .make 1561 928 1562,
  .make 1562 929 1563,
  .make 1563 930 1564]
private def block120 : List Gate := [
  .make 1564 931 1565,
  .make 1565 932 1566,
  .make 1566 933 1567,
  .make 1567 934 1568,
  .make 1568 935 1569,
  .make 1569 936 1570]
private def block126 : List Gate := [
  .make 1570 937 1571,
  .make 1571 938 1572,
  .make 1572 939 1573,
  .make 1573 940 1574,
  .cx 1574 1556,
  .x 1556,
  .pop 1573 940 1574,
  .pop 1572 939 1573,
  .pop 1571 938 1572,
  .pop 1570 937 1571,
  .pop 1569 936 1570,
  .pop 1568 935 1569,
  .pop 1567 934 1568,
  .pop 1566 933 1567,
  .pop 1565 932 1566,
  .pop 1564 931 1565,
  .pop 1563 930 1564,
  .pop 1562 929 1563,
  .pop 1561 928 1562,
  .pop 1560 927 1561,
  .pop 1559 926 1560,
  .pop 1558 925 1559,
  .pop 1557 924 1558,
  .pop 922 923 1557,
  .x 940,
  .x 939,
  .x 938,
  .x 937,
  .x 936,
  .x 935,
  .x 934,
  .x 933,
  .x 932,
  .x 931]
private def block160 : List Gate := [
  .x 930,
  .x 929,
  .x 928,
  .x 927,
  .x 926,
  .x 925,
  .x 924,
  .x 923,
  .x 922,
  .x 1557,
  .cx 407 1557,
  .make 922 1557 1558,
  .make 923 1558 1559,
  .make 924 1559 1560,
  .make 925 1560 1561,
  .make 926 1561 1562,
  .make 927 1562 1563,
  .make 928 1563 1564,
  .make 929 1564 1565,
  .make 930 1565 1566,
  .make 931 1566 1567,
  .make 932 1567 1568,
  .make 933 1568 1569,
  .make 934 1569 1570,
  .make 935 1570 1571,
  .make 936 1571 1572,
  .make 937 1572 1573,
  .make 938 1573 1574,
  .make 939 1574 1575,
  .cx 1575 940,
  .pop 939 1574 1575,
  .cx 1574 939]
private def block192 : List Gate := [
  .pop 938 1573 1574,
  .cx 1573 938,
  .pop 937 1572 1573,
  .cx 1572 937,
  .pop 936 1571 1572,
  .cx 1571 936,
  .pop 935 1570 1571,
  .cx 1570 935]
private def block200 : List Gate := [
  .pop 934 1569 1570,
  .cx 1569 934,
  .pop 933 1568 1569,
  .cx 1568 933,
  .pop 932 1567 1568,
  .cx 1567 932,
  .pop 931 1566 1567,
  .cx 1566 931,
  .pop 930 1565 1566,
  .cx 1565 930,
  .pop 929 1564 1565,
  .cx 1564 929,
  .pop 928 1563 1564,
  .cx 1563 928,
  .pop 927 1562 1563,
  .cx 1562 927,
  .pop 926 1561 1562,
  .cx 1561 926,
  .pop 925 1560 1561,
  .cx 1560 925,
  .pop 924 1559 1560,
  .cx 1559 924]
private def block222 : List Gate := [
  .pop 923 1558 1559,
  .cx 1558 923,
  .ccx 1556 408 923,
  .ccx 1556 409 924,
  .ccx 1556 410 925,
  .ccx 1556 411 926,
  .ccx 1556 412 927,
  .ccx 1556 413 928,
  .ccx 1556 414 929,
  .ccx 1556 415 930,
  .ccx 1556 416 931,
  .ccx 1556 417 932,
  .ccx 1556 418 933,
  .ccx 1556 419 934,
  .ccx 1556 420 935,
  .ccx 1556 421 936,
  .ccx 1556 422 937,
  .ccx 1556 423 938]
private def block240 : List Gate := [
  .ccx 1556 424 939,
  .ccx 1556 425 940,
  .make 1713 1714 1559,
  .cx 1713 1560,
  .cx 1559 1560,
  .make 1560 1284 1561,
  .cx 1561 1560,
  .make 1560 1285 1562,
  .cx 1562 1560,
  .make 1560 1286 1563,
  .cx 1563 1560,
  .make 1560 1287 1564,
  .cx 1564 1560,
  .make 1560 1288 1565,
  .cx 1565 1560,
  .make 1560 1289 1566,
  .cx 1566 1560,
  .make 1560 1290 1567,
  .cx 1567 1560,
  .make 1560 1291 1568,
  .cx 1568 1560,
  .make 1560 1292 1569,
  .cx 1569 1560,
  .make 1560 1293 1570,
  .cx 1570 1560,
  .make 1560 1294 1571,
  .cx 1571 1560,
  .make 1560 1295 1572,
  .cx 1572 1560,
  .make 1560 1296 1573,
  .cx 1573 1560,
  .make 1560 1297 1574,
  .cx 1574 1560,
  .make 1560 1298 1575,
  .cx 1575 1560,
  .cx 1559 1717,
  .cx 1561 1717,
  .cx 1562 1717,
  .cx 1563 1717,
  .cx 1564 1717]
private def block280 : List Gate := [
  .cx 1565 1717,
  .cx 1559 1576,
  .cx 1561 1576,
  .make 269 270 1577,
  .make 268 1577 1578,
  .make 267 1578 1579,
  .make 266 1579 1580,
  .make 265 1580 1581]
private def block288 : List Gate := [
  .make 264 1581 1582,
  .make 263 1582 1583,
  .make 262 1583 1584,
  .make 261 1584 1585,
  .make 260 1585 1586,
  .make 259 1586 1587,
  .make 258 1587 1588,
  .make 1562 1588 1589,
  .make 1563 1586 1590,
  .make 1564 1584 1591,
  .make 1565 1582 1592,
  .make 1566 1580 1593,
  .make 1567 1578 1594,
  .make 1568 270 1595,
  .ccx 1576 408 1716,
  .ccx 1562 409 1716,
  .ccx 1563 410 1716,
  .ccx 1564 411 1716,
  .ccx 1565 412 1716,
  .ccx 1566 413 1716,
  .ccx 1567 414 1716,
  .ccx 1568 415 1716,
  .ccx 1569 416 1716,
  .ccx 1570 417 1716,
  .ccx 1571 418 1716,
  .ccx 1572 419 1716,
  .ccx 1573 420 1716,
  .ccx 1574 421 1716,
  .ccx 1575 422 1716,
  .ccx 1560 423 1716]
private def block318 : List Gate := [
  .cx 1589 1596,
  .cx 1590 1596]
private def block320 : List Gate := [
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .make 1716 1596 1597,
  .cx 1597 1710,
  .cx 1597 1711,
  .cx 1597 1712,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943,
  .cx 1597 944,
  .cx 1597 945,
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963]
private def block360 : List Gate := [
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987]
private def block384 : List Gate := [
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003]
private def block400 : List Gate := [
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017]
private def block414 : List Gate := [
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030,
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034,
  .cx 1597 1035,
  .cx 1597 1036,
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .make 1710 1716 1598]
private def block440 : List Gate := [
  .make 1711 1598 1599,
  .make 1712 1599 1600,
  .make 941 1600 1601,
  .make 942 1601 1602,
  .make 943 1602 1603,
  .make 944 1603 1604,
  .make 945 1604 1605,
  .make 946 1605 1606,
  .make 947 1606 1607,
  .make 948 1607 1608,
  .make 949 1608 1609,
  .make 950 1609 1610,
  .make 951 1610 1611,
  .make 952 1611 1612,
  .make 953 1612 1613,
  .make 954 1613 1614,
  .make 955 1614 1615,
  .make 956 1615 1616,
  .make 957 1616 1617,
  .make 958 1617 1618,
  .make 959 1618 1619,
  .make 960 1619 1620,
  .make 961 1620 1621,
  .make 962 1621 1622,
  .make 963 1622 1623,
  .make 964 1623 1624,
  .make 965 1624 1625,
  .make 966 1625 1626,
  .make 967 1626 1627,
  .make 968 1627 1628,
  .make 969 1628 1629,
  .make 970 1629 1630,
  .make 971 1630 1631,
  .make 972 1631 1632,
  .make 973 1632 1633,
  .make 974 1633 1634,
  .make 975 1634 1635,
  .make 976 1635 1636,
  .make 977 1636 1637,
  .make 978 1637 1638]
private def block480 : List Gate := [
  .make 979 1638 1639,
  .make 980 1639 1640,
  .make 981 1640 1641,
  .make 982 1641 1642,
  .make 983 1642 1643,
  .make 984 1643 1644,
  .make 985 1644 1645,
  .make 986 1645 1646,
  .make 987 1646 1647,
  .make 988 1647 1648,
  .make 989 1648 1649,
  .make 990 1649 1650,
  .make 991 1650 1651,
  .make 992 1651 1652,
  .make 993 1652 1653,
  .make 994 1653 1654,
  .make 995 1654 1655,
  .make 996 1655 1656,
  .make 997 1656 1657,
  .make 998 1657 1658,
  .make 999 1658 1659,
  .make 1000 1659 1660,
  .make 1001 1660 1661,
  .make 1002 1661 1662,
  .make 1003 1662 1663,
  .make 1004 1663 1664,
  .make 1005 1664 1665,
  .make 1006 1665 1666,
  .make 1007 1666 1667,
  .make 1008 1667 1668]
private def block510 : List Gate := [
  .make 1009 1668 1669,
  .make 1010 1669 1670,
  .make 1011 1670 1671,
  .make 1012 1671 1672,
  .make 1013 1672 1673,
  .make 1014 1673 1674,
  .make 1015 1674 1675,
  .make 1016 1675 1676,
  .make 1017 1676 1677,
  .make 1018 1677 1678]
private def block520 : List Gate := [
  .make 1019 1678 1679,
  .make 1020 1679 1680,
  .make 1021 1680 1681,
  .make 1022 1681 1682,
  .make 1023 1682 1683,
  .make 1024 1683 1684,
  .make 1025 1684 1685,
  .make 1026 1685 1686,
  .make 1027 1686 1687,
  .make 1028 1687 1688,
  .make 1029 1688 1689,
  .make 1030 1689 1690,
  .make 1031 1690 1691,
  .make 1032 1691 1692,
  .make 1033 1692 1693,
  .make 1034 1693 1694,
  .make 1035 1694 1695,
  .make 1036 1695 1696,
  .make 1037 1696 1697,
  .make 1038 1697 1698,
  .make 1039 1698 1699,
  .make 1040 1699 1700,
  .make 1041 1700 1701,
  .cx 1701 1042,
  .pop 1041 1700 1701,
  .cx 1700 1041,
  .pop 1040 1699 1700,
  .cx 1699 1040,
  .pop 1039 1698 1699,
  .cx 1698 1039,
  .pop 1038 1697 1698,
  .cx 1697 1038,
  .pop 1037 1696 1697,
  .cx 1696 1037,
  .pop 1036 1695 1696,
  .cx 1695 1036,
  .pop 1035 1694 1695,
  .cx 1694 1035,
  .pop 1034 1693 1694,
  .cx 1693 1034]
private def block560 : List Gate := [
  .pop 1033 1692 1693,
  .cx 1692 1033,
  .pop 1032 1691 1692,
  .cx 1691 1032,
  .pop 1031 1690 1691,
  .cx 1690 1031,
  .pop 1030 1689 1690,
  .cx 1689 1030,
  .pop 1029 1688 1689,
  .cx 1688 1029,
  .pop 1028 1687 1688,
  .cx 1687 1028,
  .pop 1027 1686 1687,
  .cx 1686 1027,
  .pop 1026 1685 1686,
  .cx 1685 1026]
private def block576 : List Gate := [
  .pop 1025 1684 1685,
  .cx 1684 1025,
  .pop 1024 1683 1684,
  .cx 1683 1024,
  .pop 1023 1682 1683,
  .cx 1682 1023,
  .pop 1022 1681 1682,
  .cx 1681 1022,
  .pop 1021 1680 1681,
  .cx 1680 1021,
  .pop 1020 1679 1680,
  .cx 1679 1020,
  .pop 1019 1678 1679,
  .cx 1678 1019,
  .pop 1018 1677 1678,
  .cx 1677 1018,
  .pop 1017 1676 1677,
  .cx 1676 1017,
  .pop 1016 1675 1676,
  .cx 1675 1016,
  .pop 1015 1674 1675,
  .cx 1674 1015,
  .pop 1014 1673 1674,
  .cx 1673 1014]
private def block600 : List Gate := [
  .pop 1013 1672 1673,
  .cx 1672 1013,
  .pop 1012 1671 1672,
  .cx 1671 1012,
  .pop 1011 1670 1671,
  .cx 1670 1011]
private def block606 : List Gate := [
  .pop 1010 1669 1670,
  .cx 1669 1010,
  .pop 1009 1668 1669,
  .cx 1668 1009,
  .pop 1008 1667 1668,
  .cx 1667 1008,
  .pop 1007 1666 1667,
  .cx 1666 1007,
  .pop 1006 1665 1666,
  .cx 1665 1006,
  .pop 1005 1664 1665,
  .cx 1664 1005,
  .pop 1004 1663 1664,
  .cx 1663 1004,
  .pop 1003 1662 1663,
  .cx 1662 1003,
  .pop 1002 1661 1662,
  .cx 1661 1002,
  .pop 1001 1660 1661,
  .cx 1660 1001,
  .pop 1000 1659 1660,
  .cx 1659 1000,
  .pop 999 1658 1659,
  .cx 1658 999,
  .pop 998 1657 1658,
  .cx 1657 998,
  .pop 997 1656 1657,
  .cx 1656 997,
  .pop 996 1655 1656,
  .cx 1655 996,
  .pop 995 1654 1655,
  .cx 1654 995,
  .pop 994 1653 1654,
  .cx 1653 994]
private def block640 : List Gate := [
  .pop 993 1652 1653,
  .cx 1652 993,
  .pop 992 1651 1652,
  .cx 1651 992,
  .pop 991 1650 1651,
  .cx 1650 991,
  .pop 990 1649 1650,
  .cx 1649 990,
  .pop 989 1648 1649,
  .cx 1648 989,
  .pop 988 1647 1648,
  .cx 1647 988,
  .pop 987 1646 1647,
  .cx 1646 987,
  .pop 986 1645 1646,
  .cx 1645 986,
  .pop 985 1644 1645,
  .cx 1644 985,
  .pop 984 1643 1644,
  .cx 1643 984,
  .pop 983 1642 1643,
  .cx 1642 983,
  .pop 982 1641 1642,
  .cx 1641 982,
  .pop 981 1640 1641,
  .cx 1640 981,
  .pop 980 1639 1640,
  .cx 1639 980,
  .pop 979 1638 1639,
  .cx 1638 979,
  .pop 978 1637 1638,
  .cx 1637 978]
private def block672 : List Gate := [
  .pop 977 1636 1637,
  .cx 1636 977,
  .pop 976 1635 1636,
  .cx 1635 976,
  .pop 975 1634 1635,
  .cx 1634 975,
  .pop 974 1633 1634,
  .cx 1633 974]
private def block680 : List Gate := [
  .pop 973 1632 1633,
  .cx 1632 973,
  .pop 972 1631 1632,
  .cx 1631 972,
  .pop 971 1630 1631,
  .cx 1630 971,
  .pop 970 1629 1630,
  .cx 1629 970,
  .pop 969 1628 1629,
  .cx 1628 969,
  .pop 968 1627 1628,
  .cx 1627 968,
  .pop 967 1626 1627,
  .cx 1626 967,
  .pop 966 1625 1626,
  .cx 1625 966,
  .pop 965 1624 1625,
  .cx 1624 965,
  .pop 964 1623 1624,
  .cx 1623 964,
  .pop 963 1622 1623,
  .cx 1622 963]
private def block702 : List Gate := [
  .pop 962 1621 1622,
  .cx 1621 962,
  .pop 961 1620 1621,
  .cx 1620 961,
  .pop 960 1619 1620,
  .cx 1619 960,
  .pop 959 1618 1619,
  .cx 1618 959,
  .pop 958 1617 1618,
  .cx 1617 958,
  .pop 957 1616 1617,
  .cx 1616 957,
  .pop 956 1615 1616,
  .cx 1615 956,
  .pop 955 1614 1615,
  .cx 1614 955,
  .pop 954 1613 1614,
  .cx 1613 954]
private def block720 : List Gate := [
  .pop 953 1612 1613,
  .cx 1612 953,
  .pop 952 1611 1612,
  .cx 1611 952,
  .pop 951 1610 1611,
  .cx 1610 951,
  .pop 950 1609 1610,
  .cx 1609 950,
  .pop 949 1608 1609,
  .cx 1608 949,
  .pop 948 1607 1608,
  .cx 1607 948,
  .pop 947 1606 1607,
  .cx 1606 947,
  .pop 946 1605 1606,
  .cx 1605 946,
  .pop 945 1604 1605,
  .cx 1604 945,
  .pop 944 1603 1604,
  .cx 1603 944,
  .pop 943 1602 1603,
  .cx 1602 943,
  .pop 942 1601 1602,
  .cx 1601 942,
  .pop 941 1600 1601,
  .cx 1600 941,
  .pop 1712 1599 1600,
  .cx 1599 1712,
  .pop 1711 1598 1599,
  .cx 1598 1711,
  .pop 1710 1716 1598,
  .cx 1716 1710,
  .cx 1597 1710,
  .cx 1597 1711,
  .cx 1597 1712,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943,
  .cx 1597 944,
  .cx 1597 945]
private def block760 : List Gate := [
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953]
private def block768 : List Gate := [
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983]
private def block798 : List Gate := [
  .cx 1597 984,
  .cx 1597 985]
private def block800 : List Gate := [
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025]
private def block840 : List Gate := [
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030,
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034,
  .cx 1597 1035,
  .cx 1597 1036,
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613]
private def block864 : List Gate := [
  .cx 1560 1613,
  .cx 1042 1598,
  .ccx 1613 1598 1042,
  .cx 1042 1598,
  .cx 1041 1042,
  .ccx 1613 1042 1041,
  .cx 1041 1042,
  .cx 1040 1041,
  .ccx 1613 1041 1040,
  .cx 1040 1041,
  .cx 1039 1040,
  .ccx 1613 1040 1039,
  .cx 1039 1040,
  .cx 1038 1039,
  .ccx 1613 1039 1038,
  .cx 1038 1039]
private def block880 : List Gate := [
  .cx 1037 1038,
  .ccx 1613 1038 1037,
  .cx 1037 1038,
  .cx 1036 1037,
  .ccx 1613 1037 1036,
  .cx 1036 1037,
  .cx 1035 1036,
  .ccx 1613 1036 1035,
  .cx 1035 1036,
  .cx 1034 1035,
  .ccx 1613 1035 1034,
  .cx 1034 1035,
  .cx 1033 1034,
  .ccx 1613 1034 1033]
private def block894 : List Gate := [
  .cx 1033 1034,
  .cx 1032 1033,
  .ccx 1613 1033 1032,
  .cx 1032 1033,
  .cx 1031 1032,
  .ccx 1613 1032 1031,
  .cx 1031 1032,
  .cx 1030 1031,
  .ccx 1613 1031 1030,
  .cx 1030 1031,
  .cx 1029 1030,
  .ccx 1613 1030 1029,
  .cx 1029 1030,
  .cx 1028 1029,
  .ccx 1613 1029 1028,
  .cx 1028 1029,
  .cx 1027 1028,
  .ccx 1613 1028 1027,
  .cx 1027 1028,
  .cx 1026 1027,
  .ccx 1613 1027 1026,
  .cx 1026 1027,
  .cx 1025 1026,
  .ccx 1613 1026 1025,
  .cx 1025 1026,
  .cx 1024 1025]
private def block920 : List Gate := [
  .ccx 1613 1025 1024,
  .cx 1024 1025,
  .cx 1023 1024,
  .ccx 1613 1024 1023,
  .cx 1023 1024,
  .cx 1022 1023,
  .ccx 1613 1023 1022,
  .cx 1022 1023,
  .cx 1021 1022,
  .ccx 1613 1022 1021,
  .cx 1021 1022,
  .cx 1020 1021,
  .ccx 1613 1021 1020,
  .cx 1020 1021,
  .cx 1019 1020,
  .ccx 1613 1020 1019,
  .cx 1019 1020,
  .cx 1018 1019,
  .ccx 1613 1019 1018,
  .cx 1018 1019,
  .cx 1017 1018,
  .ccx 1613 1018 1017,
  .cx 1017 1018,
  .cx 1016 1017,
  .ccx 1613 1017 1016,
  .cx 1016 1017,
  .cx 1015 1016,
  .ccx 1613 1016 1015,
  .cx 1015 1016,
  .cx 1014 1015,
  .ccx 1613 1015 1014,
  .cx 1014 1015,
  .cx 1013 1014,
  .ccx 1613 1014 1013,
  .cx 1013 1014,
  .cx 1012 1013,
  .ccx 1613 1013 1012,
  .cx 1012 1013,
  .cx 1011 1012,
  .ccx 1613 1012 1011]
private def block960 : List Gate := [
  .cx 1011 1012,
  .cx 1010 1011,
  .ccx 1613 1011 1010,
  .cx 1010 1011,
  .cx 1009 1010,
  .ccx 1613 1010 1009,
  .cx 1009 1010,
  .cx 1008 1009,
  .ccx 1613 1009 1008,
  .cx 1008 1009,
  .cx 1007 1008,
  .ccx 1613 1008 1007,
  .cx 1007 1008,
  .cx 1006 1007,
  .ccx 1613 1007 1006,
  .cx 1006 1007,
  .cx 1005 1006,
  .ccx 1613 1006 1005,
  .cx 1005 1006,
  .cx 1004 1005,
  .ccx 1613 1005 1004,
  .cx 1004 1005,
  .cx 1003 1004,
  .ccx 1613 1004 1003,
  .cx 1003 1004,
  .cx 1002 1003,
  .ccx 1613 1003 1002,
  .cx 1002 1003,
  .cx 1001 1002,
  .ccx 1613 1002 1001]
private def block990 : List Gate := [
  .cx 1001 1002,
  .cx 1000 1001,
  .ccx 1613 1001 1000,
  .cx 1000 1001,
  .cx 999 1000,
  .ccx 1613 1000 999,
  .cx 999 1000,
  .cx 998 999,
  .ccx 1613 999 998,
  .cx 998 999]
private def block1000 : List Gate := [
  .cx 997 998,
  .ccx 1613 998 997,
  .cx 997 998,
  .cx 996 997,
  .ccx 1613 997 996,
  .cx 996 997,
  .cx 995 996,
  .ccx 1613 996 995,
  .cx 995 996,
  .cx 994 995,
  .ccx 1613 995 994,
  .cx 994 995,
  .cx 993 994,
  .ccx 1613 994 993,
  .cx 993 994,
  .cx 992 993,
  .ccx 1613 993 992,
  .cx 992 993,
  .cx 991 992,
  .ccx 1613 992 991,
  .cx 991 992,
  .cx 990 991,
  .ccx 1613 991 990,
  .cx 990 991,
  .cx 989 990,
  .ccx 1613 990 989,
  .cx 989 990,
  .cx 988 989,
  .ccx 1613 989 988,
  .cx 988 989,
  .cx 987 988,
  .ccx 1613 988 987,
  .cx 987 988,
  .cx 986 987,
  .ccx 1613 987 986,
  .cx 986 987,
  .cx 985 986,
  .ccx 1613 986 985,
  .cx 985 986,
  .cx 984 985]
private def block1040 : List Gate := [
  .ccx 1613 985 984,
  .cx 984 985,
  .cx 983 984,
  .ccx 1613 984 983,
  .cx 983 984,
  .cx 982 983,
  .ccx 1613 983 982,
  .cx 982 983,
  .cx 981 982,
  .ccx 1613 982 981,
  .cx 981 982,
  .cx 980 981,
  .ccx 1613 981 980,
  .cx 980 981,
  .cx 979 980,
  .ccx 1613 980 979]
private def block1056 : List Gate := [
  .cx 979 980,
  .cx 978 979,
  .ccx 1613 979 978,
  .cx 978 979,
  .cx 977 978,
  .ccx 1613 978 977,
  .cx 977 978,
  .cx 976 977,
  .ccx 1613 977 976,
  .cx 976 977,
  .cx 975 976,
  .ccx 1613 976 975,
  .cx 975 976,
  .cx 974 975,
  .ccx 1613 975 974,
  .cx 974 975,
  .cx 973 974,
  .ccx 1613 974 973,
  .cx 973 974,
  .cx 972 973,
  .ccx 1613 973 972,
  .cx 972 973,
  .cx 971 972,
  .ccx 1613 972 971]
private def block1080 : List Gate := [
  .cx 971 972,
  .cx 970 971,
  .ccx 1613 971 970,
  .cx 970 971,
  .cx 969 970,
  .ccx 1613 970 969]
private def block1086 : List Gate := [
  .cx 969 970,
  .cx 968 969,
  .ccx 1613 969 968,
  .cx 968 969,
  .cx 967 968,
  .ccx 1613 968 967,
  .cx 967 968,
  .cx 966 967,
  .ccx 1613 967 966,
  .cx 966 967,
  .cx 965 966,
  .ccx 1613 966 965,
  .cx 965 966,
  .cx 964 965,
  .ccx 1613 965 964,
  .cx 964 965,
  .cx 963 964,
  .ccx 1613 964 963,
  .cx 963 964,
  .cx 962 963,
  .ccx 1613 963 962,
  .cx 962 963,
  .cx 961 962,
  .ccx 1613 962 961,
  .cx 961 962,
  .cx 960 961,
  .ccx 1613 961 960,
  .cx 960 961,
  .cx 959 960,
  .ccx 1613 960 959,
  .cx 959 960,
  .cx 958 959,
  .ccx 1613 959 958,
  .cx 958 959]
private def block1120 : List Gate := [
  .cx 957 958,
  .ccx 1613 958 957,
  .cx 957 958,
  .cx 956 957,
  .ccx 1613 957 956,
  .cx 956 957,
  .cx 955 956,
  .ccx 1613 956 955,
  .cx 955 956,
  .cx 954 955,
  .ccx 1613 955 954,
  .cx 954 955,
  .cx 953 954,
  .ccx 1613 954 953,
  .cx 953 954,
  .cx 952 953,
  .ccx 1613 953 952,
  .cx 952 953,
  .cx 951 952,
  .ccx 1613 952 951,
  .cx 951 952,
  .cx 950 951,
  .ccx 1613 951 950,
  .cx 950 951,
  .cx 949 950,
  .ccx 1613 950 949,
  .cx 949 950,
  .cx 948 949,
  .ccx 1613 949 948,
  .cx 948 949,
  .cx 947 948,
  .ccx 1613 948 947]
private def block1152 : List Gate := [
  .cx 947 948,
  .cx 946 947,
  .ccx 1613 947 946,
  .cx 946 947,
  .cx 945 946,
  .ccx 1613 946 945,
  .cx 945 946,
  .cx 944 945]
private def block1160 : List Gate := [
  .ccx 1613 945 944,
  .cx 944 945,
  .cx 943 944,
  .ccx 1613 944 943,
  .cx 943 944,
  .cx 942 943,
  .ccx 1613 943 942,
  .cx 942 943,
  .cx 941 942,
  .ccx 1613 942 941,
  .cx 941 942,
  .cx 1712 941,
  .ccx 1613 941 1712,
  .cx 1712 941,
  .cx 1711 1712,
  .ccx 1613 1712 1711,
  .cx 1711 1712,
  .cx 1710 1711,
  .ccx 1613 1711 1710,
  .cx 1710 1711,
  .cx 1562 1613,
  .cx 1564 1613]
private def block1182 : List Gate := [
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1598 1600,
  .ccx 1613 1600 1598,
  .cx 1598 1600,
  .cx 1042 1599]
private def block1200 : List Gate := [
  .ccx 1613 1599 1042,
  .cx 1042 1599,
  .cx 1041 1598,
  .ccx 1613 1598 1041,
  .cx 1041 1598,
  .cx 1040 1042,
  .ccx 1613 1042 1040,
  .cx 1040 1042,
  .cx 1039 1041,
  .ccx 1613 1041 1039,
  .cx 1039 1041,
  .cx 1038 1040,
  .ccx 1613 1040 1038,
  .cx 1038 1040,
  .cx 1037 1039,
  .ccx 1613 1039 1037,
  .cx 1037 1039,
  .cx 1036 1038,
  .ccx 1613 1038 1036,
  .cx 1036 1038,
  .cx 1035 1037,
  .ccx 1613 1037 1035,
  .cx 1035 1037,
  .cx 1034 1036,
  .ccx 1613 1036 1034,
  .cx 1034 1036,
  .cx 1033 1035,
  .ccx 1613 1035 1033,
  .cx 1033 1035,
  .cx 1032 1034,
  .ccx 1613 1034 1032,
  .cx 1032 1034,
  .cx 1031 1033,
  .ccx 1613 1033 1031,
  .cx 1031 1033,
  .cx 1030 1032,
  .ccx 1613 1032 1030,
  .cx 1030 1032,
  .cx 1029 1031,
  .ccx 1613 1031 1029]
private def block1240 : List Gate := [
  .cx 1029 1031,
  .cx 1028 1030,
  .ccx 1613 1030 1028,
  .cx 1028 1030,
  .cx 1027 1029,
  .ccx 1613 1029 1027,
  .cx 1027 1029,
  .cx 1026 1028]
private def block1248 : List Gate := [
  .ccx 1613 1028 1026,
  .cx 1026 1028,
  .cx 1025 1027,
  .ccx 1613 1027 1025,
  .cx 1025 1027,
  .cx 1024 1026,
  .ccx 1613 1026 1024,
  .cx 1024 1026,
  .cx 1023 1025,
  .ccx 1613 1025 1023,
  .cx 1023 1025,
  .cx 1022 1024,
  .ccx 1613 1024 1022,
  .cx 1022 1024,
  .cx 1021 1023,
  .ccx 1613 1023 1021,
  .cx 1021 1023,
  .cx 1020 1022,
  .ccx 1613 1022 1020,
  .cx 1020 1022,
  .cx 1019 1021,
  .ccx 1613 1021 1019,
  .cx 1019 1021,
  .cx 1018 1020,
  .ccx 1613 1020 1018,
  .cx 1018 1020,
  .cx 1017 1019,
  .ccx 1613 1019 1017,
  .cx 1017 1019,
  .cx 1016 1018]
private def block1278 : List Gate := [
  .ccx 1613 1018 1016,
  .cx 1016 1018]
private def block1280 : List Gate := [
  .cx 1015 1017,
  .ccx 1613 1017 1015,
  .cx 1015 1017,
  .cx 1014 1016,
  .ccx 1613 1016 1014,
  .cx 1014 1016,
  .cx 1013 1015,
  .ccx 1613 1015 1013,
  .cx 1013 1015,
  .cx 1012 1014,
  .ccx 1613 1014 1012,
  .cx 1012 1014,
  .cx 1011 1013,
  .ccx 1613 1013 1011,
  .cx 1011 1013,
  .cx 1010 1012,
  .ccx 1613 1012 1010,
  .cx 1010 1012,
  .cx 1009 1011,
  .ccx 1613 1011 1009,
  .cx 1009 1011,
  .cx 1008 1010,
  .ccx 1613 1010 1008,
  .cx 1008 1010,
  .cx 1007 1009,
  .ccx 1613 1009 1007,
  .cx 1007 1009,
  .cx 1006 1008,
  .ccx 1613 1008 1006,
  .cx 1006 1008,
  .cx 1005 1007,
  .ccx 1613 1007 1005,
  .cx 1005 1007,
  .cx 1004 1006,
  .ccx 1613 1006 1004,
  .cx 1004 1006,
  .cx 1003 1005,
  .ccx 1613 1005 1003,
  .cx 1003 1005,
  .cx 1002 1004]
private def block1320 : List Gate := [
  .ccx 1613 1004 1002,
  .cx 1002 1004,
  .cx 1001 1003,
  .ccx 1613 1003 1001,
  .cx 1001 1003,
  .cx 1000 1002,
  .ccx 1613 1002 1000,
  .cx 1000 1002,
  .cx 999 1001,
  .ccx 1613 1001 999,
  .cx 999 1001,
  .cx 998 1000,
  .ccx 1613 1000 998,
  .cx 998 1000,
  .cx 997 999,
  .ccx 1613 999 997,
  .cx 997 999,
  .cx 996 998,
  .ccx 1613 998 996,
  .cx 996 998,
  .cx 995 997,
  .ccx 1613 997 995,
  .cx 995 997,
  .cx 994 996]
private def block1344 : List Gate := [
  .ccx 1613 996 994,
  .cx 994 996,
  .cx 993 995,
  .ccx 1613 995 993,
  .cx 993 995,
  .cx 992 994,
  .ccx 1613 994 992,
  .cx 992 994,
  .cx 991 993,
  .ccx 1613 993 991,
  .cx 991 993,
  .cx 990 992,
  .ccx 1613 992 990,
  .cx 990 992,
  .cx 989 991,
  .ccx 1613 991 989]
private def block1360 : List Gate := [
  .cx 989 991,
  .cx 988 990,
  .ccx 1613 990 988,
  .cx 988 990,
  .cx 987 989,
  .ccx 1613 989 987,
  .cx 987 989,
  .cx 986 988,
  .ccx 1613 988 986,
  .cx 986 988,
  .cx 985 987,
  .ccx 1613 987 985,
  .cx 985 987,
  .cx 984 986]
private def block1374 : List Gate := [
  .ccx 1613 986 984,
  .cx 984 986,
  .cx 983 985,
  .ccx 1613 985 983,
  .cx 983 985,
  .cx 982 984,
  .ccx 1613 984 982,
  .cx 982 984,
  .cx 981 983,
  .ccx 1613 983 981,
  .cx 981 983,
  .cx 980 982,
  .ccx 1613 982 980,
  .cx 980 982,
  .cx 979 981,
  .ccx 1613 981 979,
  .cx 979 981,
  .cx 978 980,
  .ccx 1613 980 978,
  .cx 978 980,
  .cx 977 979,
  .ccx 1613 979 977,
  .cx 977 979,
  .cx 976 978,
  .ccx 1613 978 976,
  .cx 976 978]
private def block1400 : List Gate := [
  .cx 975 977,
  .ccx 1613 977 975,
  .cx 975 977,
  .cx 974 976,
  .ccx 1613 976 974,
  .cx 974 976,
  .cx 973 975,
  .ccx 1613 975 973,
  .cx 973 975,
  .cx 972 974,
  .ccx 1613 974 972,
  .cx 972 974,
  .cx 971 973,
  .ccx 1613 973 971,
  .cx 971 973,
  .cx 970 972,
  .ccx 1613 972 970,
  .cx 970 972,
  .cx 969 971,
  .ccx 1613 971 969,
  .cx 969 971,
  .cx 968 970,
  .ccx 1613 970 968,
  .cx 968 970,
  .cx 967 969,
  .ccx 1613 969 967,
  .cx 967 969,
  .cx 966 968,
  .ccx 1613 968 966,
  .cx 966 968,
  .cx 965 967,
  .ccx 1613 967 965,
  .cx 965 967,
  .cx 964 966,
  .ccx 1613 966 964,
  .cx 964 966,
  .cx 963 965,
  .ccx 1613 965 963,
  .cx 963 965,
  .cx 962 964]
private def block1440 : List Gate := [
  .ccx 1613 964 962,
  .cx 962 964,
  .cx 961 963,
  .ccx 1613 963 961,
  .cx 961 963,
  .cx 960 962,
  .ccx 1613 962 960,
  .cx 960 962,
  .cx 959 961,
  .ccx 1613 961 959,
  .cx 959 961,
  .cx 958 960,
  .ccx 1613 960 958,
  .cx 958 960,
  .cx 957 959,
  .ccx 1613 959 957,
  .cx 957 959,
  .cx 956 958,
  .ccx 1613 958 956,
  .cx 956 958,
  .cx 955 957,
  .ccx 1613 957 955,
  .cx 955 957,
  .cx 954 956,
  .ccx 1613 956 954,
  .cx 954 956,
  .cx 953 955,
  .ccx 1613 955 953,
  .cx 953 955,
  .cx 952 954]
private def block1470 : List Gate := [
  .ccx 1613 954 952,
  .cx 952 954,
  .cx 951 953,
  .ccx 1613 953 951,
  .cx 951 953,
  .cx 950 952,
  .ccx 1613 952 950,
  .cx 950 952,
  .cx 949 951,
  .ccx 1613 951 949]
private def block1480 : List Gate := [
  .cx 949 951,
  .cx 948 950,
  .ccx 1613 950 948,
  .cx 948 950,
  .cx 947 949,
  .ccx 1613 949 947,
  .cx 947 949,
  .cx 946 948,
  .ccx 1613 948 946,
  .cx 946 948,
  .cx 945 947,
  .ccx 1613 947 945,
  .cx 945 947,
  .cx 944 946,
  .ccx 1613 946 944,
  .cx 944 946,
  .cx 943 945,
  .ccx 1613 945 943,
  .cx 943 945,
  .cx 942 944,
  .ccx 1613 944 942,
  .cx 942 944,
  .cx 941 943,
  .ccx 1613 943 941,
  .cx 941 943,
  .cx 1712 942,
  .ccx 1613 942 1712,
  .cx 1712 942,
  .cx 1711 941,
  .ccx 1613 941 1711,
  .cx 1711 941,
  .cx 1710 1712,
  .ccx 1613 1712 1710,
  .cx 1710 1712,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613]
private def block1520 : List Gate := [
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1600 1604,
  .ccx 1613 1604 1600,
  .cx 1600 1604,
  .cx 1599 1603,
  .ccx 1613 1603 1599,
  .cx 1599 1603]
private def block1536 : List Gate := [
  .cx 1598 1602,
  .ccx 1613 1602 1598,
  .cx 1598 1602,
  .cx 1042 1601,
  .ccx 1613 1601 1042,
  .cx 1042 1601,
  .cx 1041 1600,
  .ccx 1613 1600 1041,
  .cx 1041 1600,
  .cx 1040 1599,
  .ccx 1613 1599 1040,
  .cx 1040 1599,
  .cx 1039 1598,
  .ccx 1613 1598 1039,
  .cx 1039 1598,
  .cx 1038 1042,
  .ccx 1613 1042 1038,
  .cx 1038 1042,
  .cx 1037 1041,
  .ccx 1613 1041 1037,
  .cx 1037 1041,
  .cx 1036 1040,
  .ccx 1613 1040 1036,
  .cx 1036 1040]
private def block1560 : List Gate := [
  .cx 1035 1039,
  .ccx 1613 1039 1035,
  .cx 1035 1039,
  .cx 1034 1038,
  .ccx 1613 1038 1034,
  .cx 1034 1038]
private def block1566 : List Gate := [
  .cx 1033 1037,
  .ccx 1613 1037 1033,
  .cx 1033 1037,
  .cx 1032 1036,
  .ccx 1613 1036 1032,
  .cx 1032 1036,
  .cx 1031 1035,
  .ccx 1613 1035 1031,
  .cx 1031 1035,
  .cx 1030 1034,
  .ccx 1613 1034 1030,
  .cx 1030 1034,
  .cx 1029 1033,
  .ccx 1613 1033 1029,
  .cx 1029 1033,
  .cx 1028 1032,
  .ccx 1613 1032 1028,
  .cx 1028 1032,
  .cx 1027 1031,
  .ccx 1613 1031 1027,
  .cx 1027 1031,
  .cx 1026 1030,
  .ccx 1613 1030 1026,
  .cx 1026 1030,
  .cx 1025 1029,
  .ccx 1613 1029 1025,
  .cx 1025 1029,
  .cx 1024 1028,
  .ccx 1613 1028 1024,
  .cx 1024 1028,
  .cx 1023 1027,
  .ccx 1613 1027 1023,
  .cx 1023 1027,
  .cx 1022 1026]
private def block1600 : List Gate := [
  .ccx 1613 1026 1022,
  .cx 1022 1026,
  .cx 1021 1025,
  .ccx 1613 1025 1021,
  .cx 1021 1025,
  .cx 1020 1024,
  .ccx 1613 1024 1020,
  .cx 1020 1024,
  .cx 1019 1023,
  .ccx 1613 1023 1019,
  .cx 1019 1023,
  .cx 1018 1022,
  .ccx 1613 1022 1018,
  .cx 1018 1022,
  .cx 1017 1021,
  .ccx 1613 1021 1017,
  .cx 1017 1021,
  .cx 1016 1020,
  .ccx 1613 1020 1016,
  .cx 1016 1020,
  .cx 1015 1019,
  .ccx 1613 1019 1015,
  .cx 1015 1019,
  .cx 1014 1018,
  .ccx 1613 1018 1014,
  .cx 1014 1018,
  .cx 1013 1017,
  .ccx 1613 1017 1013,
  .cx 1013 1017,
  .cx 1012 1016,
  .ccx 1613 1016 1012,
  .cx 1012 1016]
private def block1632 : List Gate := [
  .cx 1011 1015,
  .ccx 1613 1015 1011,
  .cx 1011 1015,
  .cx 1010 1014,
  .ccx 1613 1014 1010,
  .cx 1010 1014,
  .cx 1009 1013,
  .ccx 1613 1013 1009]
private def block1640 : List Gate := [
  .cx 1009 1013,
  .cx 1008 1012,
  .ccx 1613 1012 1008,
  .cx 1008 1012,
  .cx 1007 1011,
  .ccx 1613 1011 1007,
  .cx 1007 1011,
  .cx 1006 1010,
  .ccx 1613 1010 1006,
  .cx 1006 1010,
  .cx 1005 1009,
  .ccx 1613 1009 1005,
  .cx 1005 1009,
  .cx 1004 1008,
  .ccx 1613 1008 1004,
  .cx 1004 1008,
  .cx 1003 1007,
  .ccx 1613 1007 1003,
  .cx 1003 1007,
  .cx 1002 1006,
  .ccx 1613 1006 1002,
  .cx 1002 1006]
private def block1662 : List Gate := [
  .cx 1001 1005,
  .ccx 1613 1005 1001,
  .cx 1001 1005,
  .cx 1000 1004,
  .ccx 1613 1004 1000,
  .cx 1000 1004,
  .cx 999 1003,
  .ccx 1613 1003 999,
  .cx 999 1003,
  .cx 998 1002,
  .ccx 1613 1002 998,
  .cx 998 1002,
  .cx 997 1001,
  .ccx 1613 1001 997,
  .cx 997 1001,
  .cx 996 1000,
  .ccx 1613 1000 996,
  .cx 996 1000]
private def block1680 : List Gate := [
  .cx 995 999,
  .ccx 1613 999 995,
  .cx 995 999,
  .cx 994 998,
  .ccx 1613 998 994,
  .cx 994 998,
  .cx 993 997,
  .ccx 1613 997 993,
  .cx 993 997,
  .cx 992 996,
  .ccx 1613 996 992,
  .cx 992 996,
  .cx 991 995,
  .ccx 1613 995 991,
  .cx 991 995,
  .cx 990 994,
  .ccx 1613 994 990,
  .cx 990 994,
  .cx 989 993,
  .ccx 1613 993 989,
  .cx 989 993,
  .cx 988 992,
  .ccx 1613 992 988,
  .cx 988 992,
  .cx 987 991,
  .ccx 1613 991 987,
  .cx 987 991,
  .cx 986 990,
  .ccx 1613 990 986,
  .cx 986 990,
  .cx 985 989,
  .ccx 1613 989 985,
  .cx 985 989,
  .cx 984 988,
  .ccx 1613 988 984,
  .cx 984 988,
  .cx 983 987,
  .ccx 1613 987 983,
  .cx 983 987,
  .cx 982 986]
private def block1720 : List Gate := [
  .ccx 1613 986 982,
  .cx 982 986,
  .cx 981 985,
  .ccx 1613 985 981,
  .cx 981 985,
  .cx 980 984,
  .ccx 1613 984 980,
  .cx 980 984]
private def block1728 : List Gate := [
  .cx 979 983,
  .ccx 1613 983 979,
  .cx 979 983,
  .cx 978 982,
  .ccx 1613 982 978,
  .cx 978 982,
  .cx 977 981,
  .ccx 1613 981 977,
  .cx 977 981,
  .cx 976 980,
  .ccx 1613 980 976,
  .cx 976 980,
  .cx 975 979,
  .ccx 1613 979 975,
  .cx 975 979,
  .cx 974 978,
  .ccx 1613 978 974,
  .cx 974 978,
  .cx 973 977,
  .ccx 1613 977 973,
  .cx 973 977,
  .cx 972 976,
  .ccx 1613 976 972,
  .cx 972 976,
  .cx 971 975,
  .ccx 1613 975 971,
  .cx 971 975,
  .cx 970 974,
  .ccx 1613 974 970,
  .cx 970 974]
private def block1758 : List Gate := [
  .cx 969 973,
  .ccx 1613 973 969]
private def block1760 : List Gate := [
  .cx 969 973,
  .cx 968 972,
  .ccx 1613 972 968,
  .cx 968 972,
  .cx 967 971,
  .ccx 1613 971 967,
  .cx 967 971,
  .cx 966 970,
  .ccx 1613 970 966,
  .cx 966 970,
  .cx 965 969,
  .ccx 1613 969 965,
  .cx 965 969,
  .cx 964 968,
  .ccx 1613 968 964,
  .cx 964 968,
  .cx 963 967,
  .ccx 1613 967 963,
  .cx 963 967,
  .cx 962 966,
  .ccx 1613 966 962,
  .cx 962 966,
  .cx 961 965,
  .ccx 1613 965 961,
  .cx 961 965,
  .cx 960 964,
  .ccx 1613 964 960,
  .cx 960 964,
  .cx 959 963,
  .ccx 1613 963 959,
  .cx 959 963,
  .cx 958 962,
  .ccx 1613 962 958,
  .cx 958 962,
  .cx 957 961,
  .ccx 1613 961 957,
  .cx 957 961,
  .cx 956 960,
  .ccx 1613 960 956,
  .cx 956 960]
private def block1800 : List Gate := [
  .cx 955 959,
  .ccx 1613 959 955,
  .cx 955 959,
  .cx 954 958,
  .ccx 1613 958 954,
  .cx 954 958,
  .cx 953 957,
  .ccx 1613 957 953,
  .cx 953 957,
  .cx 952 956,
  .ccx 1613 956 952,
  .cx 952 956,
  .cx 951 955,
  .ccx 1613 955 951,
  .cx 951 955,
  .cx 950 954,
  .ccx 1613 954 950,
  .cx 950 954,
  .cx 949 953,
  .ccx 1613 953 949,
  .cx 949 953,
  .cx 948 952,
  .ccx 1613 952 948,
  .cx 948 952]
private def block1824 : List Gate := [
  .cx 947 951,
  .ccx 1613 951 947,
  .cx 947 951,
  .cx 946 950,
  .ccx 1613 950 946,
  .cx 946 950,
  .cx 945 949,
  .ccx 1613 949 945,
  .cx 945 949,
  .cx 944 948,
  .ccx 1613 948 944,
  .cx 944 948,
  .cx 943 947,
  .ccx 1613 947 943,
  .cx 943 947,
  .cx 942 946]
private def block1840 : List Gate := [
  .ccx 1613 946 942,
  .cx 942 946,
  .cx 941 945,
  .ccx 1613 945 941,
  .cx 941 945,
  .cx 1712 944,
  .ccx 1613 944 1712,
  .cx 1712 944,
  .cx 1711 943,
  .ccx 1613 943 1711,
  .cx 1711 943,
  .cx 1710 942,
  .ccx 1613 942 1710,
  .cx 1710 942]
private def block1854 : List Gate := [
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1604 1612,
  .ccx 1613 1612 1604,
  .cx 1604 1612,
  .cx 1603 1611,
  .ccx 1613 1611 1603,
  .cx 1603 1611,
  .cx 1602 1610,
  .ccx 1613 1610 1602,
  .cx 1602 1610,
  .cx 1601 1609]
private def block1880 : List Gate := [
  .ccx 1613 1609 1601,
  .cx 1601 1609,
  .cx 1600 1608,
  .ccx 1613 1608 1600,
  .cx 1600 1608,
  .cx 1599 1607,
  .ccx 1613 1607 1599,
  .cx 1599 1607,
  .cx 1598 1606,
  .ccx 1613 1606 1598,
  .cx 1598 1606,
  .cx 1042 1605,
  .ccx 1613 1605 1042,
  .cx 1042 1605,
  .cx 1041 1604,
  .ccx 1613 1604 1041,
  .cx 1041 1604,
  .cx 1040 1603,
  .ccx 1613 1603 1040,
  .cx 1040 1603,
  .cx 1039 1602,
  .ccx 1613 1602 1039,
  .cx 1039 1602,
  .cx 1038 1601,
  .ccx 1613 1601 1038,
  .cx 1038 1601,
  .cx 1037 1600,
  .ccx 1613 1600 1037,
  .cx 1037 1600,
  .cx 1036 1599,
  .ccx 1613 1599 1036,
  .cx 1036 1599,
  .cx 1035 1598,
  .ccx 1613 1598 1035,
  .cx 1035 1598,
  .cx 1034 1042,
  .ccx 1613 1042 1034,
  .cx 1034 1042,
  .cx 1033 1041,
  .ccx 1613 1041 1033]
private def block1920 : List Gate := [
  .cx 1033 1041,
  .cx 1032 1040,
  .ccx 1613 1040 1032,
  .cx 1032 1040,
  .cx 1031 1039,
  .ccx 1613 1039 1031,
  .cx 1031 1039,
  .cx 1030 1038,
  .ccx 1613 1038 1030,
  .cx 1030 1038,
  .cx 1029 1037,
  .ccx 1613 1037 1029,
  .cx 1029 1037,
  .cx 1028 1036,
  .ccx 1613 1036 1028,
  .cx 1028 1036,
  .cx 1027 1035,
  .ccx 1613 1035 1027,
  .cx 1027 1035,
  .cx 1026 1034,
  .ccx 1613 1034 1026,
  .cx 1026 1034,
  .cx 1025 1033,
  .ccx 1613 1033 1025,
  .cx 1025 1033,
  .cx 1024 1032,
  .ccx 1613 1032 1024,
  .cx 1024 1032,
  .cx 1023 1031,
  .ccx 1613 1031 1023]
private def block1950 : List Gate := [
  .cx 1023 1031,
  .cx 1022 1030,
  .ccx 1613 1030 1022,
  .cx 1022 1030,
  .cx 1021 1029,
  .ccx 1613 1029 1021,
  .cx 1021 1029,
  .cx 1020 1028,
  .ccx 1613 1028 1020,
  .cx 1020 1028]
private def block1960 : List Gate := [
  .cx 1019 1027,
  .ccx 1613 1027 1019,
  .cx 1019 1027,
  .cx 1018 1026,
  .ccx 1613 1026 1018,
  .cx 1018 1026,
  .cx 1017 1025,
  .ccx 1613 1025 1017,
  .cx 1017 1025,
  .cx 1016 1024,
  .ccx 1613 1024 1016,
  .cx 1016 1024,
  .cx 1015 1023,
  .ccx 1613 1023 1015,
  .cx 1015 1023,
  .cx 1014 1022,
  .ccx 1613 1022 1014,
  .cx 1014 1022,
  .cx 1013 1021,
  .ccx 1613 1021 1013,
  .cx 1013 1021,
  .cx 1012 1020,
  .ccx 1613 1020 1012,
  .cx 1012 1020,
  .cx 1011 1019,
  .ccx 1613 1019 1011,
  .cx 1011 1019,
  .cx 1010 1018,
  .ccx 1613 1018 1010,
  .cx 1010 1018,
  .cx 1009 1017,
  .ccx 1613 1017 1009,
  .cx 1009 1017,
  .cx 1008 1016,
  .ccx 1613 1016 1008,
  .cx 1008 1016,
  .cx 1007 1015,
  .ccx 1613 1015 1007,
  .cx 1007 1015,
  .cx 1006 1014]
private def block2000 : List Gate := [
  .ccx 1613 1014 1006,
  .cx 1006 1014,
  .cx 1005 1013,
  .ccx 1613 1013 1005,
  .cx 1005 1013,
  .cx 1004 1012,
  .ccx 1613 1012 1004,
  .cx 1004 1012,
  .cx 1003 1011,
  .ccx 1613 1011 1003,
  .cx 1003 1011,
  .cx 1002 1010,
  .ccx 1613 1010 1002,
  .cx 1002 1010,
  .cx 1001 1009,
  .ccx 1613 1009 1001]
private def block2016 : List Gate := [
  .cx 1001 1009,
  .cx 1000 1008,
  .ccx 1613 1008 1000,
  .cx 1000 1008,
  .cx 999 1007,
  .ccx 1613 1007 999,
  .cx 999 1007,
  .cx 998 1006,
  .ccx 1613 1006 998,
  .cx 998 1006,
  .cx 997 1005,
  .ccx 1613 1005 997,
  .cx 997 1005,
  .cx 996 1004,
  .ccx 1613 1004 996,
  .cx 996 1004,
  .cx 995 1003,
  .ccx 1613 1003 995,
  .cx 995 1003,
  .cx 994 1002,
  .ccx 1613 1002 994,
  .cx 994 1002,
  .cx 993 1001,
  .ccx 1613 1001 993]
private def block2040 : List Gate := [
  .cx 993 1001,
  .cx 992 1000,
  .ccx 1613 1000 992,
  .cx 992 1000,
  .cx 991 999,
  .ccx 1613 999 991]
private def block2046 : List Gate := [
  .cx 991 999,
  .cx 990 998,
  .ccx 1613 998 990,
  .cx 990 998,
  .cx 989 997,
  .ccx 1613 997 989,
  .cx 989 997,
  .cx 988 996,
  .ccx 1613 996 988,
  .cx 988 996,
  .cx 987 995,
  .ccx 1613 995 987,
  .cx 987 995,
  .cx 986 994,
  .ccx 1613 994 986,
  .cx 986 994,
  .cx 985 993,
  .ccx 1613 993 985,
  .cx 985 993,
  .cx 984 992,
  .ccx 1613 992 984,
  .cx 984 992,
  .cx 983 991,
  .ccx 1613 991 983,
  .cx 983 991,
  .cx 982 990,
  .ccx 1613 990 982,
  .cx 982 990,
  .cx 981 989,
  .ccx 1613 989 981,
  .cx 981 989,
  .cx 980 988,
  .ccx 1613 988 980,
  .cx 980 988]
private def block2080 : List Gate := [
  .cx 979 987,
  .ccx 1613 987 979,
  .cx 979 987,
  .cx 978 986,
  .ccx 1613 986 978,
  .cx 978 986,
  .cx 977 985,
  .ccx 1613 985 977,
  .cx 977 985,
  .cx 976 984,
  .ccx 1613 984 976,
  .cx 976 984,
  .cx 975 983,
  .ccx 1613 983 975,
  .cx 975 983,
  .cx 974 982,
  .ccx 1613 982 974,
  .cx 974 982,
  .cx 973 981,
  .ccx 1613 981 973,
  .cx 973 981,
  .cx 972 980,
  .ccx 1613 980 972,
  .cx 972 980,
  .cx 971 979,
  .ccx 1613 979 971,
  .cx 971 979,
  .cx 970 978,
  .ccx 1613 978 970,
  .cx 970 978,
  .cx 969 977,
  .ccx 1613 977 969]
private def block2112 : List Gate := [
  .cx 969 977,
  .cx 968 976,
  .ccx 1613 976 968,
  .cx 968 976,
  .cx 967 975,
  .ccx 1613 975 967,
  .cx 967 975,
  .cx 966 974]
private def block2120 : List Gate := [
  .ccx 1613 974 966,
  .cx 966 974,
  .cx 965 973,
  .ccx 1613 973 965,
  .cx 965 973,
  .cx 964 972,
  .ccx 1613 972 964,
  .cx 964 972,
  .cx 963 971,
  .ccx 1613 971 963,
  .cx 963 971,
  .cx 962 970,
  .ccx 1613 970 962,
  .cx 962 970,
  .cx 961 969,
  .ccx 1613 969 961,
  .cx 961 969,
  .cx 960 968,
  .ccx 1613 968 960,
  .cx 960 968,
  .cx 959 967,
  .ccx 1613 967 959]
private def block2142 : List Gate := [
  .cx 959 967,
  .cx 958 966,
  .ccx 1613 966 958,
  .cx 958 966,
  .cx 957 965,
  .ccx 1613 965 957,
  .cx 957 965,
  .cx 956 964,
  .ccx 1613 964 956,
  .cx 956 964,
  .cx 955 963,
  .ccx 1613 963 955,
  .cx 955 963,
  .cx 954 962,
  .ccx 1613 962 954,
  .cx 954 962,
  .cx 953 961,
  .ccx 1613 961 953]
private def block2160 : List Gate := [
  .cx 953 961,
  .cx 952 960,
  .ccx 1613 960 952,
  .cx 952 960,
  .cx 951 959,
  .ccx 1613 959 951,
  .cx 951 959,
  .cx 950 958,
  .ccx 1613 958 950,
  .cx 950 958,
  .cx 949 957,
  .ccx 1613 957 949,
  .cx 949 957,
  .cx 948 956,
  .ccx 1613 956 948,
  .cx 948 956,
  .cx 947 955,
  .ccx 1613 955 947,
  .cx 947 955,
  .cx 946 954,
  .ccx 1613 954 946,
  .cx 946 954,
  .cx 945 953,
  .ccx 1613 953 945,
  .cx 945 953,
  .cx 944 952,
  .ccx 1613 952 944,
  .cx 944 952,
  .cx 943 951,
  .ccx 1613 951 943,
  .cx 943 951,
  .cx 942 950,
  .ccx 1613 950 942,
  .cx 942 950,
  .cx 941 949,
  .ccx 1613 949 941,
  .cx 941 949,
  .cx 1712 948,
  .ccx 1613 948 1712,
  .cx 1712 948]
private def block2200 : List Gate := [
  .cx 1711 947,
  .ccx 1613 947 1711,
  .cx 1711 947,
  .cx 1710 946,
  .ccx 1613 946 1710,
  .cx 1710 946,
  .cx 1569 1613,
  .cx 1570 1613]
private def block2208 : List Gate := [
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .x 1613,
  .cx 1597 1613,
  .ccx 1576 1716 408,
  .ccx 1576 1613 409,
  .ccx 1562 1716 409,
  .ccx 1562 1613 410,
  .ccx 1563 1716 410,
  .ccx 1563 1613 411,
  .ccx 1564 1716 411,
  .ccx 1564 1613 412,
  .ccx 1565 1716 412,
  .ccx 1565 1613 413,
  .ccx 1566 1716 413,
  .ccx 1566 1613 414,
  .ccx 1567 1716 414,
  .ccx 1567 1613 415,
  .ccx 1568 1716 415,
  .ccx 1568 1613 416,
  .ccx 1569 1716 416,
  .ccx 1569 1613 417,
  .ccx 1570 1716 417,
  .ccx 1570 1613 418,
  .ccx 1571 1716 418,
  .ccx 1571 1613 419]
private def block2238 : List Gate := [
  .ccx 1572 1716 419,
  .ccx 1572 1613 420]
private def block2240 : List Gate := [
  .ccx 1573 1716 420,
  .ccx 1573 1613 421,
  .ccx 1574 1716 421,
  .ccx 1574 1613 422,
  .ccx 1575 1716 422,
  .ccx 1575 1613 423,
  .ccx 1560 1716 423,
  .ccx 1560 1613 424,
  .cx 1576 1614,
  .cx 1710 408,
  .ccx 1614 408 1710,
  .cx 1562 1614,
  .cx 1711 409,
  .ccx 1614 409 1711,
  .cx 1563 1614,
  .cx 1712 410,
  .ccx 1614 410 1712,
  .cx 1564 1614,
  .cx 941 411,
  .ccx 1614 411 941,
  .cx 1565 1614,
  .cx 942 412,
  .ccx 1614 412 942,
  .cx 1566 1614,
  .cx 943 413,
  .ccx 1614 413 943,
  .cx 1567 1614,
  .cx 944 414,
  .ccx 1614 414 944,
  .cx 1568 1614,
  .cx 945 415,
  .ccx 1614 415 945,
  .cx 1569 1614,
  .cx 946 416,
  .ccx 1614 416 946,
  .cx 1570 1614,
  .cx 947 417,
  .ccx 1614 417 947,
  .cx 1571 1614,
  .cx 948 418]
private def block2280 : List Gate := [
  .ccx 1614 418 948,
  .cx 1572 1614,
  .cx 419 949,
  .cx 949 419,
  .ccx 1614 949 419,
  .cx 1573 1614,
  .cx 420 950,
  .cx 950 420,
  .ccx 1614 950 420,
  .cx 1574 1614,
  .cx 421 951,
  .cx 951 421,
  .ccx 1614 951 421,
  .cx 1575 1614,
  .cx 422 952,
  .cx 952 422,
  .ccx 1614 952 422,
  .cx 1560 1614,
  .cx 423 953,
  .cx 953 423,
  .ccx 1614 953 423,
  .cx 424 954,
  .cx 954 424,
  .ccx 1614 954 424]
private def block2304 : List Gate := [
  .cx 425 955,
  .cx 955 425,
  .ccx 1614 955 425,
  .cx 1560 1614,
  .cx 1575 1614,
  .cx 1574 1614,
  .cx 1573 1614,
  .cx 1572 1614,
  .cx 1571 1614,
  .cx 1570 1614,
  .cx 1569 1614,
  .cx 1568 1614,
  .cx 1567 1614,
  .cx 1566 1614,
  .cx 1565 1614,
  .cx 1564 1614]
private def block2320 : List Gate := [
  .cx 1563 1614,
  .cx 1562 1614,
  .cx 1576 1614,
  .cx 1597 1613,
  .x 1613,
  .pop 1716 1596 1597,
  .cx 1589 1596,
  .cx 1590 1596,
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596]
private def block2334 : List Gate := [
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .pop 1568 270 1595,
  .pop 1567 1578 1594,
  .pop 1566 1580 1593,
  .pop 1565 1582 1592,
  .pop 1564 1584 1591,
  .pop 1563 1586 1590,
  .pop 1562 1588 1589,
  .pop 258 1587 1588,
  .pop 259 1586 1587,
  .pop 260 1585 1586,
  .pop 261 1584 1585,
  .pop 262 1583 1584,
  .pop 263 1582 1583,
  .pop 264 1581 1582,
  .pop 265 1580 1581,
  .pop 266 1579 1580,
  .pop 267 1578 1579,
  .pop 268 1577 1578,
  .pop 269 270 1577]
private def block2360 : List Gate := [
  .cx 1559 1576,
  .cx 1561 1576,
  .cx 1575 1560,
  .pop 1560 1298 1575,
  .cx 1574 1560,
  .pop 1560 1297 1574,
  .cx 1573 1560,
  .pop 1560 1296 1573,
  .cx 1572 1560,
  .pop 1560 1295 1572,
  .cx 1571 1560,
  .pop 1560 1294 1571,
  .cx 1570 1560,
  .pop 1560 1293 1570,
  .cx 1569 1560,
  .pop 1560 1292 1569,
  .cx 1568 1560,
  .pop 1560 1291 1568,
  .cx 1567 1560,
  .pop 1560 1290 1567,
  .cx 1566 1560,
  .pop 1560 1289 1566,
  .cx 1565 1560,
  .pop 1560 1288 1565,
  .cx 1564 1560,
  .pop 1560 1287 1564,
  .cx 1563 1560,
  .pop 1560 1286 1563,
  .cx 1562 1560,
  .pop 1560 1285 1562,
  .cx 1561 1560,
  .pop 1560 1284 1561,
  .cx 1713 1560,
  .cx 1559 1560,
  .pop 1713 1714 1559]
private theorem check2360 : bitCheck block2360 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff80002ffffe00000 <<< 1556) := by decide +kernel
private def suffix2360 := block2360 ++ ([]:List Gate)
private theorem valid2360 : bitCheck suffix2360 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff80002ffffe00000 <<< 1556) := bit_join block2360 ([]:List Gate) _ (0xfffffffffffffffff80002ffffefffe8 <<< 1556) _ check2360 rfl
private theorem check2334 : bitCheck block2334 (0xfffffffffffffffff80002ffffe00000 <<< 1556) = some (0xfffffffffffffffff800020000000000 <<< 1556) := by decide +kernel
private def suffix2334 := block2334 ++ suffix2360
private theorem valid2334 : bitCheck suffix2334 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800020000000000 <<< 1556) := bit_join block2334 suffix2360 _ (0xfffffffffffffffff80002ffffe00000 <<< 1556) _ check2334 valid2360
private theorem check2320 : bitCheck block2320 (0xfffffffffffffffff800020000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2320 := block2320 ++ suffix2334
private theorem valid2320 : bitCheck suffix2320 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2320 suffix2334 _ (0xfffffffffffffffff800020000000000 <<< 1556) _ check2320 valid2334
private theorem check2304 : bitCheck block2304 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2304 := block2304 ++ suffix2320
private theorem valid2304 : bitCheck suffix2304 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2304 suffix2320 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2304 valid2320
private theorem check2280 : bitCheck block2280 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2280 := block2280 ++ suffix2304
private theorem valid2280 : bitCheck suffix2280 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2280 suffix2304 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2280 valid2304
private theorem check2240 : bitCheck block2240 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2240 := block2240 ++ suffix2280
private theorem valid2240 : bitCheck suffix2240 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2240 suffix2280 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2240 valid2280
private theorem check2238 : bitCheck block2238 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2238 := block2238 ++ suffix2240
private theorem valid2238 : bitCheck suffix2238 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2238 suffix2240 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2238 valid2240
private theorem check2208 : bitCheck block2208 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2208 := block2208 ++ suffix2238
private theorem valid2208 : bitCheck suffix2208 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2208 suffix2238 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2208 valid2238
private theorem check2200 : bitCheck block2200 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2200 := block2200 ++ suffix2208
private theorem valid2200 : bitCheck suffix2200 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2200 suffix2208 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2200 valid2208
private theorem check2160 : bitCheck block2160 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2160 := block2160 ++ suffix2200
private theorem valid2160 : bitCheck suffix2160 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2160 suffix2200 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2160 valid2200
private theorem check2142 : bitCheck block2142 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2142 := block2142 ++ suffix2160
private theorem valid2142 : bitCheck suffix2142 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2142 suffix2160 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2142 valid2160
private theorem check2120 : bitCheck block2120 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2120 := block2120 ++ suffix2142
private theorem valid2120 : bitCheck suffix2120 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2120 suffix2142 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2120 valid2142
private theorem check2112 : bitCheck block2112 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2112 := block2112 ++ suffix2120
private theorem valid2112 : bitCheck suffix2112 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2112 suffix2120 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2112 valid2120
private theorem check2080 : bitCheck block2080 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2080 := block2080 ++ suffix2112
private theorem valid2080 : bitCheck suffix2080 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2080 suffix2112 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2080 valid2112
private theorem check2046 : bitCheck block2046 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2046 := block2046 ++ suffix2080
private theorem valid2046 : bitCheck suffix2046 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2046 suffix2080 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2046 valid2080
private theorem check2040 : bitCheck block2040 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2040 := block2040 ++ suffix2046
private theorem valid2040 : bitCheck suffix2040 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2040 suffix2046 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2040 valid2046
private theorem check2016 : bitCheck block2016 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2016 := block2016 ++ suffix2040
private theorem valid2016 : bitCheck suffix2016 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2016 suffix2040 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2016 valid2040
private theorem check2000 : bitCheck block2000 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2000 := block2000 ++ suffix2016
private theorem valid2000 : bitCheck suffix2000 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block2000 suffix2016 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check2000 valid2016
private theorem check1960 : bitCheck block1960 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1960 := block1960 ++ suffix2000
private theorem valid1960 : bitCheck suffix1960 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1960 suffix2000 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1960 valid2000
private theorem check1950 : bitCheck block1950 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1950 := block1950 ++ suffix1960
private theorem valid1950 : bitCheck suffix1950 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1950 suffix1960 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1950 valid1960
private theorem check1920 : bitCheck block1920 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1920 := block1920 ++ suffix1950
private theorem valid1920 : bitCheck suffix1920 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1920 suffix1950 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1920 valid1950
private theorem check1880 : bitCheck block1880 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1880 := block1880 ++ suffix1920
private theorem valid1880 : bitCheck suffix1880 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1880 suffix1920 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1880 valid1920
private theorem check1854 : bitCheck block1854 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1854 := block1854 ++ suffix1880
private theorem valid1854 : bitCheck suffix1854 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1854 suffix1880 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1854 valid1880
private theorem check1840 : bitCheck block1840 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1840 := block1840 ++ suffix1854
private theorem valid1840 : bitCheck suffix1840 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1840 suffix1854 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1840 valid1854
private theorem check1824 : bitCheck block1824 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1824 := block1824 ++ suffix1840
private theorem valid1824 : bitCheck suffix1824 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1824 suffix1840 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1824 valid1840
private theorem check1800 : bitCheck block1800 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1800 := block1800 ++ suffix1824
private theorem valid1800 : bitCheck suffix1800 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1800 suffix1824 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1800 valid1824
private theorem check1760 : bitCheck block1760 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1760 := block1760 ++ suffix1800
private theorem valid1760 : bitCheck suffix1760 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1760 suffix1800 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1760 valid1800
private theorem check1758 : bitCheck block1758 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1758 := block1758 ++ suffix1760
private theorem valid1758 : bitCheck suffix1758 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1758 suffix1760 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1758 valid1760
private theorem check1728 : bitCheck block1728 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1728 := block1728 ++ suffix1758
private theorem valid1728 : bitCheck suffix1728 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1728 suffix1758 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1728 valid1758
private theorem check1720 : bitCheck block1720 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1720 := block1720 ++ suffix1728
private theorem valid1720 : bitCheck suffix1720 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1720 suffix1728 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1720 valid1728
private theorem check1680 : bitCheck block1680 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1680 := block1680 ++ suffix1720
private theorem valid1680 : bitCheck suffix1680 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1680 suffix1720 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1680 valid1720
private theorem check1662 : bitCheck block1662 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1662 := block1662 ++ suffix1680
private theorem valid1662 : bitCheck suffix1662 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1662 suffix1680 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1662 valid1680
private theorem check1640 : bitCheck block1640 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1640 := block1640 ++ suffix1662
private theorem valid1640 : bitCheck suffix1640 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1640 suffix1662 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1640 valid1662
private theorem check1632 : bitCheck block1632 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1632 := block1632 ++ suffix1640
private theorem valid1632 : bitCheck suffix1632 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1632 suffix1640 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1632 valid1640
private theorem check1600 : bitCheck block1600 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1600 := block1600 ++ suffix1632
private theorem valid1600 : bitCheck suffix1600 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1600 suffix1632 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1600 valid1632
private theorem check1566 : bitCheck block1566 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1566 := block1566 ++ suffix1600
private theorem valid1566 : bitCheck suffix1566 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1566 suffix1600 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1566 valid1600
private theorem check1560 : bitCheck block1560 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1560 := block1560 ++ suffix1566
private theorem valid1560 : bitCheck suffix1560 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1560 suffix1566 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1560 valid1566
private theorem check1536 : bitCheck block1536 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1536 := block1536 ++ suffix1560
private theorem valid1536 : bitCheck suffix1536 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1536 suffix1560 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1536 valid1560
private theorem check1520 : bitCheck block1520 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1520 := block1520 ++ suffix1536
private theorem valid1520 : bitCheck suffix1520 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1520 suffix1536 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1520 valid1536
private theorem check1480 : bitCheck block1480 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1480 := block1480 ++ suffix1520
private theorem valid1480 : bitCheck suffix1480 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1480 suffix1520 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1480 valid1520
private theorem check1470 : bitCheck block1470 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1470 := block1470 ++ suffix1480
private theorem valid1470 : bitCheck suffix1470 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1470 suffix1480 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1470 valid1480
private theorem check1440 : bitCheck block1440 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1440 := block1440 ++ suffix1470
private theorem valid1440 : bitCheck suffix1440 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1440 suffix1470 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1440 valid1470
private theorem check1400 : bitCheck block1400 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1400 := block1400 ++ suffix1440
private theorem valid1400 : bitCheck suffix1400 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1400 suffix1440 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1400 valid1440
private theorem check1374 : bitCheck block1374 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1374 := block1374 ++ suffix1400
private theorem valid1374 : bitCheck suffix1374 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1374 suffix1400 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1374 valid1400
private theorem check1360 : bitCheck block1360 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1360 := block1360 ++ suffix1374
private theorem valid1360 : bitCheck suffix1360 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1360 suffix1374 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1360 valid1374
private theorem check1344 : bitCheck block1344 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1344 := block1344 ++ suffix1360
private theorem valid1344 : bitCheck suffix1344 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1344 suffix1360 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1344 valid1360
private theorem check1320 : bitCheck block1320 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1320 := block1320 ++ suffix1344
private theorem valid1320 : bitCheck suffix1320 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1320 suffix1344 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1320 valid1344
private theorem check1280 : bitCheck block1280 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1280 := block1280 ++ suffix1320
private theorem valid1280 : bitCheck suffix1280 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1280 suffix1320 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1280 valid1320
private theorem check1278 : bitCheck block1278 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1278 := block1278 ++ suffix1280
private theorem valid1278 : bitCheck suffix1278 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1278 suffix1280 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1278 valid1280
private theorem check1248 : bitCheck block1248 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1248 := block1248 ++ suffix1278
private theorem valid1248 : bitCheck suffix1248 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1248 suffix1278 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1248 valid1278
private theorem check1240 : bitCheck block1240 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1240 := block1240 ++ suffix1248
private theorem valid1240 : bitCheck suffix1240 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1240 suffix1248 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1240 valid1248
private theorem check1200 : bitCheck block1200 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1200 := block1200 ++ suffix1240
private theorem valid1200 : bitCheck suffix1200 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1200 suffix1240 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1200 valid1240
private theorem check1182 : bitCheck block1182 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1182 := block1182 ++ suffix1200
private theorem valid1182 : bitCheck suffix1182 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1182 suffix1200 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1182 valid1200
private theorem check1160 : bitCheck block1160 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1160 := block1160 ++ suffix1182
private theorem valid1160 : bitCheck suffix1160 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1160 suffix1182 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1160 valid1182
private theorem check1152 : bitCheck block1152 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1152 := block1152 ++ suffix1160
private theorem valid1152 : bitCheck suffix1152 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1152 suffix1160 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1152 valid1160
private theorem check1120 : bitCheck block1120 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1120 := block1120 ++ suffix1152
private theorem valid1120 : bitCheck suffix1120 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1120 suffix1152 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1120 valid1152
private theorem check1086 : bitCheck block1086 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1086 := block1086 ++ suffix1120
private theorem valid1086 : bitCheck suffix1086 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1086 suffix1120 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1086 valid1120
private theorem check1080 : bitCheck block1080 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1080 := block1080 ++ suffix1086
private theorem valid1080 : bitCheck suffix1080 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1080 suffix1086 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1080 valid1086
private theorem check1056 : bitCheck block1056 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1056 := block1056 ++ suffix1080
private theorem valid1056 : bitCheck suffix1056 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1056 suffix1080 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1056 valid1080
private theorem check1040 : bitCheck block1040 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1040 := block1040 ++ suffix1056
private theorem valid1040 : bitCheck suffix1040 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1040 suffix1056 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1040 valid1056
private theorem check1000 : bitCheck block1000 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1000 := block1000 ++ suffix1040
private theorem valid1000 : bitCheck suffix1000 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block1000 suffix1040 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check1000 valid1040
private theorem check990 : bitCheck block990 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix990 := block990 ++ suffix1000
private theorem valid990 : bitCheck suffix990 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block990 suffix1000 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check990 valid1000
private theorem check960 : bitCheck block960 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix960 := block960 ++ suffix990
private theorem valid960 : bitCheck suffix960 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block960 suffix990 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check960 valid990
private theorem check920 : bitCheck block920 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix920 := block920 ++ suffix960
private theorem valid920 : bitCheck suffix920 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block920 suffix960 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check920 valid960
private theorem check894 : bitCheck block894 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix894 := block894 ++ suffix920
private theorem valid894 : bitCheck suffix894 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block894 suffix920 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check894 valid920
private theorem check880 : bitCheck block880 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix880 := block880 ++ suffix894
private theorem valid880 : bitCheck suffix880 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block880 suffix894 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check880 valid894
private theorem check864 : bitCheck block864 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix864 := block864 ++ suffix880
private theorem valid864 : bitCheck suffix864 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block864 suffix880 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check864 valid880
private theorem check840 : bitCheck block840 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix840 := block840 ++ suffix864
private theorem valid840 : bitCheck suffix840 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block840 suffix864 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check840 valid864
private theorem check800 : bitCheck block800 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix800 := block800 ++ suffix840
private theorem valid800 : bitCheck suffix800 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block800 suffix840 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check800 valid840
private theorem check798 : bitCheck block798 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix798 := block798 ++ suffix800
private theorem valid798 : bitCheck suffix798 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block798 suffix800 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check798 valid800
private theorem check768 : bitCheck block768 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix768 := block768 ++ suffix798
private theorem valid768 : bitCheck suffix768 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block768 suffix798 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check768 valid798
private theorem check760 : bitCheck block760 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix760 := block760 ++ suffix768
private theorem valid760 : bitCheck suffix760 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block760 suffix768 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check760 valid768
private theorem check720 : bitCheck block720 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix720 := block720 ++ suffix760
private theorem valid720 : bitCheck suffix720 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffff800000000000000 <<< 1556) := bit_join block720 suffix760 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check720 valid760
private theorem check702 : bitCheck block702 (0xfffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffff80000000000000000 <<< 1556) := by decide +kernel
private def suffix702 := block702 ++ suffix720
private theorem valid702 : bitCheck suffix702 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffff80000000000000000 <<< 1556) := bit_join block702 suffix720 _ (0xfffffffffffffffff800000000000000 <<< 1556) _ check702 valid720
private theorem check680 : bitCheck block680 (0xfffffffffffffff80000000000000000 <<< 1556) = some (0xffffffffffffc0000000000000000000 <<< 1556) := by decide +kernel
private def suffix680 := block680 ++ suffix702
private theorem valid680 : bitCheck suffix680 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffffffffffc0000000000000000000 <<< 1556) := bit_join block680 suffix702 _ (0xfffffffffffffff80000000000000000 <<< 1556) _ check680 valid702
private theorem check672 : bitCheck block672 (0xffffffffffffc0000000000000000000 <<< 1556) = some (0xfffffffffffc00000000000000000000 <<< 1556) := by decide +kernel
private def suffix672 := block672 ++ suffix680
private theorem valid672 : bitCheck suffix672 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffc00000000000000000000 <<< 1556) := bit_join block672 suffix680 _ (0xffffffffffffc0000000000000000000 <<< 1556) _ check672 valid680
private theorem check640 : bitCheck block640 (0xfffffffffffc00000000000000000000 <<< 1556) = some (0xfffffffc000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix640 := block640 ++ suffix672
private theorem valid640 : bitCheck suffix640 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffc000000000000000000000000 <<< 1556) := bit_join block640 suffix672 _ (0xfffffffffffc00000000000000000000 <<< 1556) _ check640 valid672
private theorem check606 : bitCheck block606 (0xfffffffc000000000000000000000000 <<< 1556) = some (0xfff80000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix606 := block606 ++ suffix640
private theorem valid606 : bitCheck suffix606 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfff80000000000000000000000000000 <<< 1556) := bit_join block606 suffix640 _ (0xfffffffc000000000000000000000000 <<< 1556) _ check606 valid640
private theorem check600 : bitCheck block600 (0xfff80000000000000000000000000000 <<< 1556) = some (0xffc00000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix600 := block600 ++ suffix606
private theorem valid600 : bitCheck suffix600 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffc00000000000000000000000000000 <<< 1556) := bit_join block600 suffix606 _ (0xfff80000000000000000000000000000 <<< 1556) _ check600 valid606
private theorem check576 : bitCheck block576 (0xffc00000000000000000000000000000 <<< 1556) = some 0 := by decide +kernel
private def suffix576 := block576 ++ suffix600
private theorem valid576 : bitCheck suffix576 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some 0 := bit_join block576 suffix600 _ (0xffc00000000000000000000000000000 <<< 1556) _ check576 valid600
private theorem check560 : bitCheck block560 0 = some 0 := by decide +kernel
private def suffix560 := block560 ++ suffix576
private theorem valid560 : bitCheck suffix560 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some 0 := bit_join block560 suffix576 _ 0 _ check560 valid576
private theorem check520 : bitCheck block520 0 = some (0x3fffff8000000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix520 := block520 ++ suffix560
private theorem valid520 : bitCheck suffix520 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffff8000000000000000000000000000000 <<< 1556) := bit_join block520 suffix560 _ 0 _ check520 valid560
private theorem check510 : bitCheck block510 (0x3fffff8000000000000000000000000000000 <<< 1556) = some (0x3fffffffe0000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix510 := block510 ++ suffix520
private theorem valid510 : bitCheck suffix510 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffe0000000000000000000000000000 <<< 1556) := bit_join block510 suffix520 _ (0x3fffff8000000000000000000000000000000 <<< 1556) _ check510 valid520
private theorem check480 : bitCheck block480 (0x3fffffffe0000000000000000000000000000 <<< 1556) = some (0x3fffffffffffffff800000000000000000000 <<< 1556) := by decide +kernel
private def suffix480 := block480 ++ suffix510
private theorem valid480 : bitCheck suffix480 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffff800000000000000000000 <<< 1556) := bit_join block480 suffix510 _ (0x3fffffffe0000000000000000000000000000 <<< 1556) _ check480 valid510
private theorem check440 : bitCheck block440 (0x3fffffffffffffff800000000000000000000 <<< 1556) = some (0x3fffffffffffffffffffffffff80000000000 <<< 1556) := by decide +kernel
private def suffix440 := block440 ++ suffix480
private theorem valid440 : bitCheck suffix440 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffff80000000000 <<< 1556) := bit_join block440 suffix480 _ (0x3fffffffffffffff800000000000000000000 <<< 1556) _ check440 valid480
private theorem check414 : bitCheck block414 (0x3fffffffffffffffffffffffff80000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix414 := block414 ++ suffix440
private theorem valid414 : bitCheck suffix414 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block414 suffix440 _ (0x3fffffffffffffffffffffffff80000000000 <<< 1556) _ check414 valid440
private theorem check400 : bitCheck block400 (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix400 := block400 ++ suffix414
private theorem valid400 : bitCheck suffix400 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block400 suffix414 _ (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) _ check400 valid414
private theorem check384 : bitCheck block384 (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix384 := block384 ++ suffix400
private theorem valid384 : bitCheck suffix384 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block384 suffix400 _ (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) _ check384 valid400
private theorem check360 : bitCheck block360 (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix360 := block360 ++ suffix384
private theorem valid360 : bitCheck suffix360 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block360 suffix384 _ (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) _ check360 valid384
private theorem check320 : bitCheck block320 (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) := by decide +kernel
private def suffix320 := block320 ++ suffix360
private theorem valid320 : bitCheck suffix320 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) := bit_join block320 suffix360 _ (0x3fffffffffffffffffffffffffc0000000000 <<< 1556) _ check320 valid360
private theorem check318 : bitCheck block318 (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) := by decide +kernel
private def suffix318 := block318 ++ suffix320
private theorem valid318 : bitCheck suffix318 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) := bit_join block318 suffix320 _ (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) _ check318 valid320
private theorem check288 : bitCheck block288 (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) = some (0x3fffffffffffffffffffffffffefffc000000 <<< 1556) := by decide +kernel
private def suffix288 := block288 ++ suffix318
private theorem valid288 : bitCheck suffix288 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffefffc000000 <<< 1556) := bit_join block288 suffix318 _ (0x3fffffffffffffffffffffffffe0000000000 <<< 1556) _ check288 valid318
private theorem check280 : bitCheck block280 (0x3fffffffffffffffffffffffffefffc000000 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffe00000 <<< 1556) := by decide +kernel
private def suffix280 := block280 ++ suffix288
private theorem valid280 : bitCheck suffix280 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffe00000 <<< 1556) := bit_join block280 suffix288 _ (0x3fffffffffffffffffffffffffefffc000000 <<< 1556) _ check280 valid288
private theorem check240 : bitCheck block240 (0x3fffffffffffffffffffffffffeffffe00000 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffefffe8 <<< 1556) := by decide +kernel
private def suffix240 := block240 ++ suffix280
private theorem valid240 : bitCheck suffix240 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffefffe8 <<< 1556) := bit_join block240 suffix280 _ (0x3fffffffffffffffffffffffffeffffe00000 <<< 1556) _ check240 valid280
private theorem check222 : bitCheck block222 (0x3fffffffffffffffffffffffffeffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffefffe0 <<< 1556) := by decide +kernel
private def suffix222 := block222 ++ suffix240
private theorem valid222 : bitCheck suffix222 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffefffe0 <<< 1556) := bit_join block222 suffix240 _ (0x3fffffffffffffffffffffffffeffffefffe8 <<< 1556) _ check222 valid240
private theorem check200 : bitCheck block200 (0x3fffffffffffffffffffffffffeffffefffe0 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) := by decide +kernel
private def suffix200 := block200 ++ suffix222
private theorem valid200 : bitCheck suffix200 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) := bit_join block200 suffix222 _ (0x3fffffffffffffffffffffffffeffffefffe0 <<< 1556) _ check200 valid222
private theorem check192 : bitCheck block192 (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffe80000 <<< 1556) := by decide +kernel
private def suffix192 := block192 ++ suffix200
private theorem valid192 : bitCheck suffix192 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffe80000 <<< 1556) := bit_join block192 suffix200 _ (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) _ check192 valid200
private theorem check160 : bitCheck block160 (0x3fffffffffffffffffffffffffeffffe80000 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffc <<< 1556) := by decide +kernel
private def suffix160 := block160 ++ suffix192
private theorem valid160 : bitCheck suffix160 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffc <<< 1556) := bit_join block160 suffix192 _ (0x3fffffffffffffffffffffffffeffffe80000 <<< 1556) _ check160 valid192
private theorem check126 : bitCheck block126 (0x3fffffffffffffffffffffffffeffffeffffc <<< 1556) = some (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) := by decide +kernel
private def suffix126 := block126 ++ suffix160
private theorem valid126 : bitCheck suffix126 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) := bit_join block126 suffix160 _ (0x3fffffffffffffffffffffffffeffffeffffc <<< 1556) _ check126 valid160
private theorem check120 : bitCheck block120 (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffe00 <<< 1556) := by decide +kernel
private def suffix120 := block120 ++ suffix126
private theorem valid120 : bitCheck suffix120 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffe00 <<< 1556) := bit_join block120 suffix126 _ (0x3fffffffffffffffffffffffffeffffef8000 <<< 1556) _ check120 valid126
private theorem check96 : bitCheck block96 (0x3fffffffffffffffffffffffffeffffeffe00 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix96 := block96 ++ suffix120
private theorem valid96 : bitCheck suffix96 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block96 suffix120 _ (0x3fffffffffffffffffffffffffeffffeffe00 <<< 1556) _ check96 valid120
private theorem check80 : bitCheck block80 (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix80 := block80 ++ suffix96
private theorem valid80 : bitCheck suffix80 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block80 suffix96 _ (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check80 valid96
private theorem check40 : bitCheck block40 (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix40 := block40 ++ suffix80
private theorem valid40 : bitCheck suffix40 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block40 suffix80 _ (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check40 valid80
private theorem check30 : bitCheck block30 (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix30 := block30 ++ suffix40
private theorem valid30 : bitCheck suffix30 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block30 suffix40 _ (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check30 valid40
private theorem check0 : bitCheck block0 (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix0 := block0 ++ suffix30
private theorem valid0 : bitCheck suffix0 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block0 suffix30 _ (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check0 valid30
private def group0 := suffix0
private theorem cert0 : bitCheck group0 (0xfffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556) := valid0
private def ops := group0 ++ (group1 ++ group2)
private theorem fPart0 : Partial.leave240Part0 = GateMirror.forward block0 ++ GateMirror.forward block30 ++ GateMirror.forward block40 ++ GateMirror.forward block80 := by rfl
private theorem fPart1 : Partial.leave240Part1 = GateMirror.forward block96 ++ GateMirror.forward block120 ++ GateMirror.forward block126 ++ GateMirror.forward block160 := by rfl
private theorem fPart2 : Partial.leave240Part2 = GateMirror.forward block192 ++ GateMirror.forward block200 ++ GateMirror.forward block222 ++ GateMirror.forward block240 ++ GateMirror.forward block280 := by rfl
private theorem fPart3 : Partial.leave240Part3 = GateMirror.forward block288 ++ GateMirror.forward block318 ++ GateMirror.forward block320 ++ GateMirror.forward block360 := by rfl
private theorem fPart4 : Partial.leave240Part4 = GateMirror.forward block384 ++ GateMirror.forward block400 ++ GateMirror.forward block414 ++ GateMirror.forward block440 := by rfl
private theorem fPart5 : Partial.leave240Part5 = GateMirror.forward block480 ++ GateMirror.forward block510 ++ GateMirror.forward block520 ++ GateMirror.forward block560 := by rfl
private theorem fPart6 : Partial.leave240Part6 = GateMirror.forward block576 ++ GateMirror.forward block600 ++ GateMirror.forward block606 ++ GateMirror.forward block640 := by rfl
private theorem fPart7 : Partial.leave240Part7 = GateMirror.forward block672 ++ GateMirror.forward block680 ++ GateMirror.forward block702 ++ GateMirror.forward block720 ++ GateMirror.forward block760 := by rfl
private theorem fPart8 : Partial.leave240Part8 = GateMirror.forward block768 ++ GateMirror.forward block798 ++ GateMirror.forward block800 ++ GateMirror.forward block840 := by rfl
private theorem fPart9 : Partial.leave240Part9 = GateMirror.forward block864 ++ GateMirror.forward block880 ++ GateMirror.forward block894 ++ GateMirror.forward block920 := by rfl
private theorem fPart10 : Partial.leave240Part10 = GateMirror.forward block960 ++ GateMirror.forward block990 ++ GateMirror.forward block1000 ++ GateMirror.forward block1040 := by rfl
private theorem fPart11 : Partial.leave240Part11 = GateMirror.forward block1056 ++ GateMirror.forward block1080 ++ GateMirror.forward block1086 ++ GateMirror.forward block1120 := by rfl
private theorem fPart12 : Partial.leave240Part12 = GateMirror.forward block1152 ++ GateMirror.forward block1160 ++ GateMirror.forward block1182 ++ GateMirror.forward block1200 ++ GateMirror.forward block1240 := by rfl
private theorem fPart13 : Partial.leave240Part13 = GateMirror.forward block1248 ++ GateMirror.forward block1278 ++ GateMirror.forward block1280 ++ GateMirror.forward block1320 := by rfl
private theorem fPart14 : Partial.leave240Part14 = GateMirror.forward block1344 ++ GateMirror.forward block1360 ++ GateMirror.forward block1374 ++ GateMirror.forward block1400 := by rfl
private theorem fPart15 : Partial.leave240Part15 = GateMirror.forward block1440 ++ GateMirror.forward block1470 ++ GateMirror.forward block1480 ++ GateMirror.forward block1520 := by rfl
private theorem fPart16 : Partial.leave240Part16 = GateMirror.forward block1536 ++ GateMirror.forward block1560 ++ GateMirror.forward block1566 ++ GateMirror.forward block1600 := by rfl
private theorem fPart17 : Partial.leave240Part17 = GateMirror.forward block1632 ++ GateMirror.forward block1640 ++ GateMirror.forward block1662 ++ GateMirror.forward block1680 ++ GateMirror.forward block1720 := by rfl
private theorem fPart18 : Partial.leave240Part18 = GateMirror.forward block1728 ++ GateMirror.forward block1758 ++ GateMirror.forward block1760 ++ GateMirror.forward block1800 := by rfl
private theorem fPart19 : Partial.leave240Part19 = GateMirror.forward block1824 ++ GateMirror.forward block1840 ++ GateMirror.forward block1854 ++ GateMirror.forward block1880 := by rfl
private theorem fPart20 : Partial.leave240Part20 = GateMirror.forward block1920 ++ GateMirror.forward block1950 ++ GateMirror.forward block1960 ++ GateMirror.forward block2000 := by rfl
private theorem fPart21 : Partial.leave240Part21 = GateMirror.forward block2016 ++ GateMirror.forward block2040 ++ GateMirror.forward block2046 ++ GateMirror.forward block2080 := by rfl
private theorem fPart22 : Partial.leave240Part22 = GateMirror.forward block2112 ++ GateMirror.forward block2120 ++ GateMirror.forward block2142 ++ GateMirror.forward block2160 ++ GateMirror.forward block2200 := by rfl
private theorem fPart23 : Partial.leave240Part23 = GateMirror.forward block2208 ++ GateMirror.forward block2238 ++ GateMirror.forward block2240 ++ GateMirror.forward block2280 := by rfl
private theorem fPart24 : Partial.leave240Part24 = GateMirror.forward block2304 ++ GateMirror.forward block2320 ++ GateMirror.forward block2334 ++ GateMirror.forward block2360 ++ GateMirror.forward block2395 := by rfl
private theorem fPart25 : Partial.leave240Part25 = GateMirror.forward block2400 ++ GateMirror.forward block2430 ++ GateMirror.forward block2435 ++ GateMirror.forward block2475 := by rfl
private theorem fPart26 : Partial.leave240Part26 = GateMirror.forward block2496 ++ GateMirror.forward block2515 ++ GateMirror.forward block2526 ++ GateMirror.forward block2555 := by rfl
private theorem fPart27 : Partial.leave240Part27 = GateMirror.forward block2592 ++ GateMirror.forward block2595 ++ GateMirror.forward block2622 ++ GateMirror.forward block2635 ++ GateMirror.forward block2675 := by rfl
private theorem fPart28 : Partial.leave240Part28 = GateMirror.forward block2688 ++ GateMirror.forward block2715 ++ GateMirror.forward block2718 ++ GateMirror.forward block2755 := by rfl
private theorem fPart29 : Partial.leave240Part29 = GateMirror.forward block2784 ++ GateMirror.forward block2795 ++ GateMirror.forward block2814 ++ GateMirror.forward block2835 ++ GateMirror.forward block2875 := by rfl
private theorem fPart30 : Partial.leave240Part30 = GateMirror.forward block2880 ++ GateMirror.forward block2910 ++ GateMirror.forward block2915 ++ GateMirror.forward block2955 := by rfl
private theorem fPart31 : Partial.leave240Part31 = GateMirror.forward block2976 ++ GateMirror.forward block2995 ++ GateMirror.forward block3006 ++ GateMirror.forward block3024 ++ GateMirror.forward block3064 := by rfl
private theorem fPart32 : Partial.leave240Part32 = GateMirror.forward block3072 ++ GateMirror.forward block3102 ++ GateMirror.forward block3104 ++ GateMirror.forward block3144 := by rfl
private theorem fPart33 : Partial.leave240Part33 = GateMirror.forward block3168 ++ GateMirror.forward block3184 ++ GateMirror.forward block3198 ++ GateMirror.forward block3224 := by rfl
private theorem fPart34 : Partial.leave240Part34 = GateMirror.forward block3264 ++ GateMirror.forward block3294 ++ GateMirror.forward block3304 ++ GateMirror.forward block3344 := by rfl
private theorem fPart35 : Partial.leave240Part35 = GateMirror.forward block3360 ++ GateMirror.forward block3384 := by rfl
private theorem fEq : GateMirror.forward ops = Partial.leave240 := by
  simp only [ops,group0,group1,group2,suffix0,suffix30,suffix40,suffix80,suffix96,suffix120,suffix126,suffix160,suffix192,suffix200,suffix222,suffix240,suffix280,suffix288,suffix318,suffix320,suffix360,suffix384,suffix400,suffix414,suffix440,suffix480,suffix510,suffix520,suffix560,suffix576,suffix600,suffix606,suffix640,suffix672,suffix680,suffix702,suffix720,suffix760,suffix768,suffix798,suffix800,suffix840,suffix864,suffix880,suffix894,suffix920,suffix960,suffix990,suffix1000,suffix1040,suffix1056,suffix1080,suffix1086,suffix1120,suffix1152,suffix1160,suffix1182,suffix1200,suffix1240,suffix1248,suffix1278,suffix1280,suffix1320,suffix1344,suffix1360,suffix1374,suffix1400,suffix1440,suffix1470,suffix1480,suffix1520,suffix1536,suffix1560,suffix1566,suffix1600,suffix1632,suffix1640,suffix1662,suffix1680,suffix1720,suffix1728,suffix1758,suffix1760,suffix1800,suffix1824,suffix1840,suffix1854,suffix1880,suffix1920,suffix1950,suffix1960,suffix2000,suffix2016,suffix2040,suffix2046,suffix2080,suffix2112,suffix2120,suffix2142,suffix2160,suffix2200,suffix2208,suffix2238,suffix2240,suffix2280,suffix2304,suffix2320,suffix2334,suffix2360,suffix2395,suffix2400,suffix2430,suffix2435,suffix2475,suffix2496,suffix2515,suffix2526,suffix2555,suffix2592,suffix2595,suffix2622,suffix2635,suffix2675,suffix2688,suffix2715,suffix2718,suffix2755,suffix2784,suffix2795,suffix2814,suffix2835,suffix2875,suffix2880,suffix2910,suffix2915,suffix2955,suffix2976,suffix2995,suffix3006,suffix3024,suffix3064,suffix3072,suffix3102,suffix3104,suffix3144,suffix3168,suffix3184,suffix3198,suffix3224,suffix3264,suffix3294,suffix3304,suffix3344,suffix3360,suffix3384,fwAppend,List.append_nil,Partial.leave240,fPart0,fPart1,fPart2,fPart3,fPart4,fPart5,fPart6,fPart7,fPart8,fPart9,fPart10,fPart11,fPart12,fPart13,fPart14,fPart15,fPart16,fPart17,fPart18,fPart19,fPart20,fPart21,fPart22,fPart23,fPart24,fPart25,fPart26,fPart27,fPart28,fPart29,fPart30,fPart31,fPart32,fPart33,fPart34,fPart35,List.append_assoc]
private theorem bPart0 : Partial.leave240InvPart0 = GateMirror.inverse block3384 ++ GateMirror.inverse block3360 ++ GateMirror.inverse block3344 ++ GateMirror.inverse block3304 ++ GateMirror.inverse block3294 := by rfl
private theorem bPart1 : Partial.leave240InvPart1 = GateMirror.inverse block3264 ++ GateMirror.inverse block3224 ++ GateMirror.inverse block3198 := by rfl
private theorem bPart2 : Partial.leave240InvPart2 = GateMirror.inverse block3184 ++ GateMirror.inverse block3168 ++ GateMirror.inverse block3144 ++ GateMirror.inverse block3104 ++ GateMirror.inverse block3102 := by rfl
private theorem bPart3 : Partial.leave240InvPart3 = GateMirror.inverse block3072 ++ GateMirror.inverse block3064 ++ GateMirror.inverse block3024 ++ GateMirror.inverse block3006 := by rfl
private theorem bPart4 : Partial.leave240InvPart4 = GateMirror.inverse block2995 ++ GateMirror.inverse block2976 ++ GateMirror.inverse block2955 ++ GateMirror.inverse block2915 ++ GateMirror.inverse block2910 := by rfl
private theorem bPart5 : Partial.leave240InvPart5 = GateMirror.inverse block2880 ++ GateMirror.inverse block2875 ++ GateMirror.inverse block2835 ++ GateMirror.inverse block2814 := by rfl
private theorem bPart6 : Partial.leave240InvPart6 = GateMirror.inverse block2795 ++ GateMirror.inverse block2784 ++ GateMirror.inverse block2755 ++ GateMirror.inverse block2718 := by rfl
private theorem bPart7 : Partial.leave240InvPart7 = GateMirror.inverse block2715 ++ GateMirror.inverse block2688 ++ GateMirror.inverse block2675 ++ GateMirror.inverse block2635 ++ GateMirror.inverse block2622 := by rfl
private theorem bPart8 : Partial.leave240InvPart8 = GateMirror.inverse block2595 ++ GateMirror.inverse block2592 ++ GateMirror.inverse block2555 ++ GateMirror.inverse block2526 := by rfl
private theorem bPart9 : Partial.leave240InvPart9 = GateMirror.inverse block2515 ++ GateMirror.inverse block2496 ++ GateMirror.inverse block2475 ++ GateMirror.inverse block2435 ++ GateMirror.inverse block2430 := by rfl
private theorem bPart10 : Partial.leave240InvPart10 = GateMirror.inverse block2400 ++ GateMirror.inverse block2395 ++ GateMirror.inverse block2360 ++ GateMirror.inverse block2334 := by rfl
private theorem bPart11 : Partial.leave240InvPart11 = GateMirror.inverse block2320 ++ GateMirror.inverse block2304 ++ GateMirror.inverse block2280 ++ GateMirror.inverse block2240 ++ GateMirror.inverse block2238 := by rfl
private theorem bPart12 : Partial.leave240InvPart12 = GateMirror.inverse block2208 ++ GateMirror.inverse block2200 ++ GateMirror.inverse block2160 ++ GateMirror.inverse block2142 := by rfl
private theorem bPart13 : Partial.leave240InvPart13 = GateMirror.inverse block2120 ++ GateMirror.inverse block2112 ++ GateMirror.inverse block2080 ++ GateMirror.inverse block2046 := by rfl
private theorem bPart14 : Partial.leave240InvPart14 = GateMirror.inverse block2040 ++ GateMirror.inverse block2016 ++ GateMirror.inverse block2000 ++ GateMirror.inverse block1960 ++ GateMirror.inverse block1950 := by rfl
private theorem bPart15 : Partial.leave240InvPart15 = GateMirror.inverse block1920 ++ GateMirror.inverse block1880 ++ GateMirror.inverse block1854 := by rfl
private theorem bPart16 : Partial.leave240InvPart16 = GateMirror.inverse block1840 ++ GateMirror.inverse block1824 ++ GateMirror.inverse block1800 ++ GateMirror.inverse block1760 ++ GateMirror.inverse block1758 := by rfl
private theorem bPart17 : Partial.leave240InvPart17 = GateMirror.inverse block1728 ++ GateMirror.inverse block1720 ++ GateMirror.inverse block1680 ++ GateMirror.inverse block1662 := by rfl
private theorem bPart18 : Partial.leave240InvPart18 = GateMirror.inverse block1640 ++ GateMirror.inverse block1632 ++ GateMirror.inverse block1600 ++ GateMirror.inverse block1566 := by rfl
private theorem bPart19 : Partial.leave240InvPart19 = GateMirror.inverse block1560 ++ GateMirror.inverse block1536 ++ GateMirror.inverse block1520 ++ GateMirror.inverse block1480 ++ GateMirror.inverse block1470 := by rfl
private theorem bPart20 : Partial.leave240InvPart20 = GateMirror.inverse block1440 ++ GateMirror.inverse block1400 ++ GateMirror.inverse block1374 := by rfl
private theorem bPart21 : Partial.leave240InvPart21 = GateMirror.inverse block1360 ++ GateMirror.inverse block1344 ++ GateMirror.inverse block1320 ++ GateMirror.inverse block1280 ++ GateMirror.inverse block1278 := by rfl
private theorem bPart22 : Partial.leave240InvPart22 = GateMirror.inverse block1248 ++ GateMirror.inverse block1240 ++ GateMirror.inverse block1200 ++ GateMirror.inverse block1182 := by rfl
private theorem bPart23 : Partial.leave240InvPart23 = GateMirror.inverse block1160 ++ GateMirror.inverse block1152 ++ GateMirror.inverse block1120 ++ GateMirror.inverse block1086 := by rfl
private theorem bPart24 : Partial.leave240InvPart24 = GateMirror.inverse block1080 ++ GateMirror.inverse block1056 ++ GateMirror.inverse block1040 ++ GateMirror.inverse block1000 ++ GateMirror.inverse block990 := by rfl
private theorem bPart25 : Partial.leave240InvPart25 = GateMirror.inverse block960 ++ GateMirror.inverse block920 ++ GateMirror.inverse block894 := by rfl
private theorem bPart26 : Partial.leave240InvPart26 = GateMirror.inverse block880 ++ GateMirror.inverse block864 ++ GateMirror.inverse block840 ++ GateMirror.inverse block800 ++ GateMirror.inverse block798 := by rfl
private theorem bPart27 : Partial.leave240InvPart27 = GateMirror.inverse block768 ++ GateMirror.inverse block760 ++ GateMirror.inverse block720 ++ GateMirror.inverse block702 := by rfl
private theorem bPart28 : Partial.leave240InvPart28 = GateMirror.inverse block680 ++ GateMirror.inverse block672 ++ GateMirror.inverse block640 ++ GateMirror.inverse block606 := by rfl
private theorem bPart29 : Partial.leave240InvPart29 = GateMirror.inverse block600 ++ GateMirror.inverse block576 ++ GateMirror.inverse block560 ++ GateMirror.inverse block520 ++ GateMirror.inverse block510 := by rfl
private theorem bPart30 : Partial.leave240InvPart30 = GateMirror.inverse block480 ++ GateMirror.inverse block440 ++ GateMirror.inverse block414 := by rfl
private theorem bPart31 : Partial.leave240InvPart31 = GateMirror.inverse block400 ++ GateMirror.inverse block384 ++ GateMirror.inverse block360 ++ GateMirror.inverse block320 ++ GateMirror.inverse block318 := by rfl
private theorem bPart32 : Partial.leave240InvPart32 = GateMirror.inverse block288 ++ GateMirror.inverse block280 ++ GateMirror.inverse block240 ++ GateMirror.inverse block222 := by rfl
private theorem bPart33 : Partial.leave240InvPart33 = GateMirror.inverse block200 ++ GateMirror.inverse block192 ++ GateMirror.inverse block160 ++ GateMirror.inverse block126 := by rfl
private theorem bPart34 : Partial.leave240InvPart34 = GateMirror.inverse block120 ++ GateMirror.inverse block96 ++ GateMirror.inverse block80 ++ GateMirror.inverse block40 ++ GateMirror.inverse block30 := by rfl
private theorem bPart35 : Partial.leave240InvPart35 = GateMirror.inverse block0 := by rfl
private theorem bEq : GateMirror.inverse ops = Partial.leave240Inv := by
  simp only [ops,group0,group1,group2,suffix0,suffix30,suffix40,suffix80,suffix96,suffix120,suffix126,suffix160,suffix192,suffix200,suffix222,suffix240,suffix280,suffix288,suffix318,suffix320,suffix360,suffix384,suffix400,suffix414,suffix440,suffix480,suffix510,suffix520,suffix560,suffix576,suffix600,suffix606,suffix640,suffix672,suffix680,suffix702,suffix720,suffix760,suffix768,suffix798,suffix800,suffix840,suffix864,suffix880,suffix894,suffix920,suffix960,suffix990,suffix1000,suffix1040,suffix1056,suffix1080,suffix1086,suffix1120,suffix1152,suffix1160,suffix1182,suffix1200,suffix1240,suffix1248,suffix1278,suffix1280,suffix1320,suffix1344,suffix1360,suffix1374,suffix1400,suffix1440,suffix1470,suffix1480,suffix1520,suffix1536,suffix1560,suffix1566,suffix1600,suffix1632,suffix1640,suffix1662,suffix1680,suffix1720,suffix1728,suffix1758,suffix1760,suffix1800,suffix1824,suffix1840,suffix1854,suffix1880,suffix1920,suffix1950,suffix1960,suffix2000,suffix2016,suffix2040,suffix2046,suffix2080,suffix2112,suffix2120,suffix2142,suffix2160,suffix2200,suffix2208,suffix2238,suffix2240,suffix2280,suffix2304,suffix2320,suffix2334,suffix2360,suffix2395,suffix2400,suffix2430,suffix2435,suffix2475,suffix2496,suffix2515,suffix2526,suffix2555,suffix2592,suffix2595,suffix2622,suffix2635,suffix2675,suffix2688,suffix2715,suffix2718,suffix2755,suffix2784,suffix2795,suffix2814,suffix2835,suffix2875,suffix2880,suffix2910,suffix2915,suffix2955,suffix2976,suffix2995,suffix3006,suffix3024,suffix3064,suffix3072,suffix3102,suffix3104,suffix3144,suffix3168,suffix3184,suffix3198,suffix3224,suffix3264,suffix3294,suffix3304,suffix3344,suffix3360,suffix3384,bwAppend,List.append_nil,Partial.leave240Inv,bPart0,bPart1,bPart2,bPart3,bPart4,bPart5,bPart6,bPart7,bPart8,bPart9,bPart10,bPart11,bPart12,bPart13,bPart14,bPart15,bPart16,bPart17,bPart18,bPart19,bPart20,bPart21,bPart22,bPart23,bPart24,bPart25,bPart26,bPart27,bPart28,bPart29,bPart30,bPart31,bPart32,bPart33,bPart34,bPart35,List.append_assoc]
private theorem len0 : block0.length=30:=rfl
private theorem len30 : block30.length=10:=rfl
private theorem len40 : block40.length=40:=rfl
private theorem len80 : block80.length=16:=rfl
private theorem len96 : block96.length=24:=rfl
private theorem len120 : block120.length=6:=rfl
private theorem len126 : block126.length=34:=rfl
private theorem len160 : block160.length=32:=rfl
private theorem len192 : block192.length=8:=rfl
private theorem len200 : block200.length=22:=rfl
private theorem len222 : block222.length=18:=rfl
private theorem len240 : block240.length=40:=rfl
private theorem len280 : block280.length=8:=rfl
private theorem len288 : block288.length=30:=rfl
private theorem len318 : block318.length=2:=rfl
private theorem len320 : block320.length=40:=rfl
private theorem len360 : block360.length=24:=rfl
private theorem len384 : block384.length=16:=rfl
private theorem len400 : block400.length=14:=rfl
private theorem len414 : block414.length=26:=rfl
private theorem len440 : block440.length=40:=rfl
private theorem len480 : block480.length=30:=rfl
private theorem len510 : block510.length=10:=rfl
private theorem len520 : block520.length=40:=rfl
private theorem len560 : block560.length=16:=rfl
private theorem len576 : block576.length=24:=rfl
private theorem len600 : block600.length=6:=rfl
private theorem len606 : block606.length=34:=rfl
private theorem len640 : block640.length=32:=rfl
private theorem len672 : block672.length=8:=rfl
private theorem len680 : block680.length=22:=rfl
private theorem len702 : block702.length=18:=rfl
private theorem len720 : block720.length=40:=rfl
private theorem len760 : block760.length=8:=rfl
private theorem len768 : block768.length=30:=rfl
private theorem len798 : block798.length=2:=rfl
private theorem len800 : block800.length=40:=rfl
private theorem len840 : block840.length=24:=rfl
private theorem len864 : block864.length=16:=rfl
private theorem len880 : block880.length=14:=rfl
private theorem len894 : block894.length=26:=rfl
private theorem len920 : block920.length=40:=rfl
private theorem len960 : block960.length=30:=rfl
private theorem len990 : block990.length=10:=rfl
private theorem len1000 : block1000.length=40:=rfl
private theorem len1040 : block1040.length=16:=rfl
private theorem len1056 : block1056.length=24:=rfl
private theorem len1080 : block1080.length=6:=rfl
private theorem len1086 : block1086.length=34:=rfl
private theorem len1120 : block1120.length=32:=rfl
private theorem len1152 : block1152.length=8:=rfl
private theorem len1160 : block1160.length=22:=rfl
private theorem len1182 : block1182.length=18:=rfl
private theorem len1200 : block1200.length=40:=rfl
private theorem len1240 : block1240.length=8:=rfl
private theorem len1248 : block1248.length=30:=rfl
private theorem len1278 : block1278.length=2:=rfl
private theorem len1280 : block1280.length=40:=rfl
private theorem len1320 : block1320.length=24:=rfl
private theorem len1344 : block1344.length=16:=rfl
private theorem len1360 : block1360.length=14:=rfl
private theorem len1374 : block1374.length=26:=rfl
private theorem len1400 : block1400.length=40:=rfl
private theorem len1440 : block1440.length=30:=rfl
private theorem len1470 : block1470.length=10:=rfl
private theorem len1480 : block1480.length=40:=rfl
private theorem len1520 : block1520.length=16:=rfl
private theorem len1536 : block1536.length=24:=rfl
private theorem len1560 : block1560.length=6:=rfl
private theorem len1566 : block1566.length=34:=rfl
private theorem len1600 : block1600.length=32:=rfl
private theorem len1632 : block1632.length=8:=rfl
private theorem len1640 : block1640.length=22:=rfl
private theorem len1662 : block1662.length=18:=rfl
private theorem len1680 : block1680.length=40:=rfl
private theorem len1720 : block1720.length=8:=rfl
private theorem len1728 : block1728.length=30:=rfl
private theorem len1758 : block1758.length=2:=rfl
private theorem len1760 : block1760.length=40:=rfl
private theorem len1800 : block1800.length=24:=rfl
private theorem len1824 : block1824.length=16:=rfl
private theorem len1840 : block1840.length=14:=rfl
private theorem len1854 : block1854.length=26:=rfl
private theorem len1880 : block1880.length=40:=rfl
private theorem len1920 : block1920.length=30:=rfl
private theorem len1950 : block1950.length=10:=rfl
private theorem len1960 : block1960.length=40:=rfl
private theorem len2000 : block2000.length=16:=rfl
private theorem len2016 : block2016.length=24:=rfl
private theorem len2040 : block2040.length=6:=rfl
private theorem len2046 : block2046.length=34:=rfl
private theorem len2080 : block2080.length=32:=rfl
private theorem len2112 : block2112.length=8:=rfl
private theorem len2120 : block2120.length=22:=rfl
private theorem len2142 : block2142.length=18:=rfl
private theorem len2160 : block2160.length=40:=rfl
private theorem len2200 : block2200.length=8:=rfl
private theorem len2208 : block2208.length=30:=rfl
private theorem len2238 : block2238.length=2:=rfl
private theorem len2240 : block2240.length=40:=rfl
private theorem len2280 : block2280.length=24:=rfl
private theorem len2304 : block2304.length=16:=rfl
private theorem len2320 : block2320.length=14:=rfl
private theorem len2334 : block2334.length=26:=rfl
private theorem len2360 : block2360.length=35:=rfl
private theorem size0 : (GateMirror.forward group0).length=2395:=by
  simp only [GateMirror.forward,List.length_map,group0,suffix0,suffix30,suffix40,suffix80,suffix96,suffix120,suffix126,suffix160,suffix192,suffix200,suffix222,suffix240,suffix280,suffix288,suffix318,suffix320,suffix360,suffix384,suffix400,suffix414,suffix440,suffix480,suffix510,suffix520,suffix560,suffix576,suffix600,suffix606,suffix640,suffix672,suffix680,suffix702,suffix720,suffix760,suffix768,suffix798,suffix800,suffix840,suffix864,suffix880,suffix894,suffix920,suffix960,suffix990,suffix1000,suffix1040,suffix1056,suffix1080,suffix1086,suffix1120,suffix1152,suffix1160,suffix1182,suffix1200,suffix1240,suffix1248,suffix1278,suffix1280,suffix1320,suffix1344,suffix1360,suffix1374,suffix1400,suffix1440,suffix1470,suffix1480,suffix1520,suffix1536,suffix1560,suffix1566,suffix1600,suffix1632,suffix1640,suffix1662,suffix1680,suffix1720,suffix1728,suffix1758,suffix1760,suffix1800,suffix1824,suffix1840,suffix1854,suffix1880,suffix1920,suffix1950,suffix1960,suffix2000,suffix2016,suffix2040,suffix2046,suffix2080,suffix2112,suffix2120,suffix2142,suffix2160,suffix2200,suffix2208,suffix2238,suffix2240,suffix2280,suffix2304,suffix2320,suffix2334,suffix2360,len0,len30,len40,len80,len96,len120,len126,len160,len192,len200,len222,len240,len280,len288,len318,len320,len360,len384,len400,len414,len440,len480,len510,len520,len560,len576,len600,len606,len640,len672,len680,len702,len720,len760,len768,len798,len800,len840,len864,len880,len894,len920,len960,len990,len1000,len1040,len1056,len1080,len1086,len1120,len1152,len1160,len1182,len1200,len1240,len1248,len1278,len1280,len1320,len1344,len1360,len1374,len1400,len1440,len1470,len1480,len1520,len1536,len1560,len1566,len1600,len1632,len1640,len1662,len1680,len1720,len1728,len1758,len1760,len1800,len1824,len1840,len1854,len1880,len1920,len1950,len1960,len2000,len2016,len2040,len2046,len2080,len2112,len2120,len2142,len2160,len2200,len2208,len2238,len2240,len2280,len2304,len2320,len2334,len2360,List.length_append,List.length_nil]
private theorem len2395 : block2395.length=5:=rfl
private theorem len2400 : block2400.length=30:=rfl
private theorem len2430 : block2430.length=5:=rfl
private theorem len2435 : block2435.length=40:=rfl
private theorem len2475 : block2475.length=21:=rfl
private theorem len2496 : block2496.length=19:=rfl
private theorem len2515 : block2515.length=11:=rfl
private theorem len2526 : block2526.length=29:=rfl
private theorem len2555 : block2555.length=37:=rfl
private theorem len2592 : block2592.length=3:=rfl
private theorem len2595 : block2595.length=27:=rfl
private theorem len2622 : block2622.length=13:=rfl
private theorem len2635 : block2635.length=40:=rfl
private theorem len2675 : block2675.length=13:=rfl
private theorem len2688 : block2688.length=27:=rfl
private theorem len2715 : block2715.length=3:=rfl
private theorem len2718 : block2718.length=37:=rfl
private theorem len2755 : block2755.length=29:=rfl
private theorem len2784 : block2784.length=11:=rfl
private theorem len2795 : block2795.length=19:=rfl
private theorem len2814 : block2814.length=21:=rfl
private theorem len2835 : block2835.length=40:=rfl
private theorem len2875 : block2875.length=5:=rfl
private theorem len2880 : block2880.length=30:=rfl
private theorem len2910 : block2910.length=5:=rfl
private theorem len2915 : block2915.length=40:=rfl
private theorem len2955 : block2955.length=21:=rfl
private theorem len2976 : block2976.length=19:=rfl
private theorem len2995 : block2995.length=11:=rfl
private theorem len3006 : block3006.length=18:=rfl
private theorem size1 : (GateMirror.forward group1).length=629:=by
  simp only [GateMirror.forward,List.length_map,group1,suffix2395,suffix2400,suffix2430,suffix2435,suffix2475,suffix2496,suffix2515,suffix2526,suffix2555,suffix2592,suffix2595,suffix2622,suffix2635,suffix2675,suffix2688,suffix2715,suffix2718,suffix2755,suffix2784,suffix2795,suffix2814,suffix2835,suffix2875,suffix2880,suffix2910,suffix2915,suffix2955,suffix2976,suffix2995,suffix3006,len2395,len2400,len2430,len2435,len2475,len2496,len2515,len2526,len2555,len2592,len2595,len2622,len2635,len2675,len2688,len2715,len2718,len2755,len2784,len2795,len2814,len2835,len2875,len2880,len2910,len2915,len2955,len2976,len2995,len3006,List.length_append,List.length_nil]
private theorem pEq : GateMirror.forward group0 = Partial.leave240.take 2395 := by
  rw [←fEq,ops,fwAppend,←size0,List.take_left]
private theorem qEq : GateMirror.forward (group0++group1) = Partial.leave240.take 3024 := by
  have lengthEq:(GateMirror.forward (group0++group1)).length=3024:=by rw [fwAppend,List.length_append,size0,size1]
  rw [←fEq,ops,←List.append_assoc,fwAppend (group0++group1) group2,←lengthEq,List.take_left]
theorem inverts (s:State) (phase:∀m,(run Partial.leave240 m s).phase=s.phase)
    (initial:∀q, 1556≤q → q≤1709 → s.basis q=false)
    (core:zeros (run (Partial.leave240.take 2395) [] s) [1560,1576,1596,1613,1614])
    (post:(run (Partial.leave240.take 3024) [] s).basis 1556=false) (m n:List Bool):
    run Partial.leave240Inv n (run Partial.leave240 m s)=s:=by
  let s1:=run (GateMirror.forward group0) [] s
  let s2:=run (GateMirror.forward group1) [] s1
  have s2e:s2=run (GateMirror.forward (group0++group1)) [] s:=by
    simp [s2,s1,GateMirror.forward,List.map_append,run_append]
  have i0:Masked s (0x3fffffffffffffffffffffffffeffffeffffe <<< 1556):=subMask (by decide +kernel) (fromRange (lo:=1556) (width:=154) (fun q h1 h2=>initial q h1 (Nat.le_of_lt_succ h2)))
  obtain ⟨h0,r0,z0⟩:=bit_sound group0 s _ _ cert0 i0
  have kc:zeros s1 [1560,1576,1596,1613,1614]:=by simpa only [s1,pEq] using core
  have i1:Masked s1 (0xfffffffffffffffffe0003fffffffff8 <<< 1556):=subMask (by decide +kernel) (bothMasks z0 (fromList kc))
  obtain ⟨h1,r1,z1⟩:=bit_sound group1 s1 _ _ cert1 i1
  have kp:zeros s2 [1556]:=by
    intro q hq
    obtain rfl: q=1556:=by simpa using hq
    rw [s2e,qEq];exact post
  have i2:Masked s2 (0x79 <<< 1556):=subMask (by decide +kernel) (bothMasks z1 (fromList kp))
  obtain ⟨h2,r2,z2⟩:=bit_sound group2 s2 _ _ cert2 i2
  have phys:∀g∈ops,proper g=true:=by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact h0 g h
    · rcases List.mem_append.mp h with h|h
      · exact h1 g h
      · exact h2 g h
  have ready:Ready s ops:=ready_append _ _ _ r0 (ready_append _ _ _ r1 r2)
  rw [←bEq,←fEq]
  exact invert ops s phys (all_prepared ops s phys (by rwa [fEq])) ready m n
end ECDSAAdd.Entrant.StairPacket.Leave240Mirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
private def block3162 : List Gate := [
  .x 1299,
  .make 1710 1299 1556,
  .x 1300,
  .make 1556 1300 1559,
  .x 1812,
  .make 1559 1812 1560]
private def block3168 : List Gate := [
  .x 1811,
  .make 1560 1811 1561,
  .x 1810,
  .make 1561 1810 1562,
  .cx 1562 1707,
  .pop 1561 1810 1562,
  .x 1810,
  .pop 1560 1811 1561,
  .x 1811,
  .pop 1559 1812 1560,
  .x 1812,
  .pop 1556 1300 1559,
  .x 1300,
  .pop 1710 1299 1556,
  .x 1299,
  .cx 941 926,
  .cx 926 941,
  .cx 941 926,
  .cx 942 927,
  .cx 927 942,
  .cx 942 927,
  .cx 943 928,
  .cx 928 943,
  .cx 943 928,
  .cx 944 929,
  .cx 929 944,
  .cx 944 929,
  .cx 945 930,
  .cx 930 945,
  .cx 945 930,
  .cx 946 931,
  .cx 931 946,
  .cx 946 931,
  .cx 947 932]
private def block3202 : List Gate := [
  .cx 932 947,
  .cx 947 932,
  .cx 948 933,
  .cx 933 948,
  .cx 948 933,
  .cx 949 934,
  .cx 934 949,
  .cx 949 934,
  .cx 950 935,
  .cx 935 950,
  .cx 950 935,
  .cx 951 936,
  .cx 936 951,
  .cx 951 936,
  .cx 952 937,
  .cx 937 952,
  .cx 952 937,
  .cx 953 938,
  .cx 938 953,
  .cx 953 938]
private def block3222 : List Gate := [
  .cx 954 939,
  .cx 939 954,
  .cx 954 939,
  .cx 955 940,
  .cx 940 955,
  .cx 955 940,
  .cx 956 941,
  .cx 941 956,
  .cx 956 941,
  .cx 957 942,
  .cx 942 957,
  .cx 957 942,
  .cx 958 943,
  .cx 943 958,
  .cx 958 943,
  .cx 959 944,
  .cx 944 959,
  .cx 959 944,
  .cx 960 945,
  .cx 945 960]
private def block3242 : List Gate := [
  .cx 960 945,
  .cx 961 946,
  .cx 946 961,
  .cx 961 946,
  .cx 962 947,
  .cx 947 962,
  .cx 962 947,
  .cx 963 948,
  .cx 948 963,
  .cx 963 948,
  .cx 964 949,
  .cx 949 964,
  .cx 964 949,
  .cx 965 950,
  .cx 950 965,
  .cx 965 950,
  .cx 966 951,
  .cx 951 966,
  .cx 966 951,
  .cx 967 952,
  .cx 952 967,
  .cx 967 952]
private def block3264 : List Gate := [
  .cx 968 953,
  .cx 953 968,
  .cx 968 953,
  .cx 969 954,
  .cx 954 969,
  .cx 969 954,
  .cx 970 955,
  .cx 955 970,
  .cx 970 955,
  .cx 971 956,
  .cx 956 971,
  .cx 971 956,
  .cx 972 957,
  .cx 957 972,
  .cx 972 957,
  .cx 973 958,
  .cx 958 973,
  .cx 973 958]
private def block3282 : List Gate := [
  .cx 974 959,
  .cx 959 974,
  .cx 974 959,
  .cx 975 960,
  .cx 960 975,
  .cx 975 960,
  .cx 976 961,
  .cx 961 976,
  .cx 976 961,
  .cx 977 962,
  .cx 962 977,
  .cx 977 962,
  .cx 978 963,
  .cx 963 978,
  .cx 978 963,
  .cx 979 964,
  .cx 964 979,
  .cx 979 964,
  .cx 980 965,
  .cx 965 980,
  .cx 980 965,
  .cx 981 966,
  .cx 966 981,
  .cx 981 966,
  .cx 982 967,
  .cx 967 982,
  .cx 982 967,
  .cx 983 968,
  .cx 968 983,
  .cx 983 968,
  .cx 984 969,
  .cx 969 984,
  .cx 984 969,
  .cx 985 970,
  .cx 970 985,
  .cx 985 970]
private def block3318 : List Gate := [
  .cx 986 971,
  .cx 971 986,
  .cx 986 971,
  .cx 987 972]
private def block3322 : List Gate := [
  .cx 972 987,
  .cx 987 972,
  .cx 988 973,
  .cx 973 988,
  .cx 988 973,
  .cx 989 974,
  .cx 974 989,
  .cx 989 974,
  .cx 990 975,
  .cx 975 990,
  .cx 990 975,
  .cx 991 976,
  .cx 976 991,
  .cx 991 976,
  .cx 992 977,
  .cx 977 992,
  .cx 992 977,
  .cx 993 978,
  .cx 978 993,
  .cx 993 978,
  .cx 994 979,
  .cx 979 994,
  .cx 994 979,
  .cx 995 980,
  .cx 980 995,
  .cx 995 980,
  .cx 996 981,
  .cx 981 996,
  .cx 996 981,
  .cx 997 982,
  .cx 982 997,
  .cx 997 982,
  .cx 998 983,
  .cx 983 998,
  .cx 998 983,
  .cx 999 984,
  .cx 984 999,
  .cx 999 984]
private def block3360 : List Gate := [
  .cx 1000 985,
  .cx 985 1000]
private def block3362 : List Gate := [
  .cx 1000 985,
  .cx 1001 986,
  .cx 986 1001,
  .cx 1001 986,
  .cx 1002 987,
  .cx 987 1002,
  .cx 1002 987,
  .cx 1003 988,
  .cx 988 1003,
  .cx 1003 988,
  .cx 1004 989,
  .cx 989 1004,
  .cx 1004 989,
  .cx 1005 990,
  .cx 990 1005,
  .cx 1005 990,
  .cx 1006 991,
  .cx 991 1006,
  .cx 1006 991,
  .cx 1007 992,
  .cx 992 1007,
  .cx 1007 992,
  .cx 1008 993,
  .cx 993 1008,
  .cx 1008 993,
  .cx 1009 994,
  .cx 994 1009,
  .cx 1009 994,
  .cx 1010 995,
  .cx 995 1010,
  .cx 1010 995,
  .cx 1011 996,
  .cx 996 1011,
  .cx 1011 996,
  .cx 1012 997,
  .cx 997 1012,
  .cx 1012 997,
  .cx 1013 998,
  .cx 998 1013,
  .cx 1013 998]
private def block3402 : List Gate := [
  .cx 1014 999,
  .cx 999 1014,
  .cx 1014 999,
  .cx 1015 1000,
  .cx 1000 1015,
  .cx 1015 1000,
  .cx 1016 1001,
  .cx 1001 1016,
  .cx 1016 1001,
  .cx 1017 1002,
  .cx 1002 1017,
  .cx 1017 1002]
private def block3414 : List Gate := [
  .cx 1018 1003,
  .cx 1003 1018,
  .cx 1018 1003,
  .cx 1019 1004,
  .cx 1004 1019,
  .cx 1019 1004,
  .cx 1020 1005,
  .cx 1005 1020,
  .cx 1020 1005,
  .cx 1021 1006,
  .cx 1006 1021,
  .cx 1021 1006,
  .cx 1022 1007,
  .cx 1007 1022,
  .cx 1022 1007,
  .cx 1023 1008,
  .cx 1008 1023,
  .cx 1023 1008,
  .cx 1024 1009,
  .cx 1009 1024,
  .cx 1024 1009,
  .cx 1025 1010,
  .cx 1010 1025,
  .cx 1025 1010,
  .cx 1026 1011,
  .cx 1011 1026,
  .cx 1026 1011,
  .cx 1027 1012]
private def block3442 : List Gate := [
  .cx 1012 1027,
  .cx 1027 1012,
  .cx 1028 1013,
  .cx 1013 1028,
  .cx 1028 1013,
  .cx 1029 1014,
  .cx 1014 1029,
  .cx 1029 1014,
  .cx 1030 1015,
  .cx 1015 1030,
  .cx 1030 1015,
  .cx 1031 1016,
  .cx 1016 1031,
  .cx 1031 1016]
private def block3456 : List Gate := [
  .cx 1032 1017,
  .cx 1017 1032,
  .cx 1032 1017,
  .cx 1033 1018,
  .cx 1018 1033,
  .cx 1033 1018,
  .cx 1034 1019,
  .cx 1019 1034,
  .cx 1034 1019,
  .cx 1035 1020,
  .cx 1020 1035,
  .cx 1035 1020,
  .cx 1036 1021,
  .cx 1021 1036,
  .cx 1036 1021,
  .cx 1037 1022,
  .cx 1022 1037,
  .cx 1037 1022,
  .cx 1038 1023,
  .cx 1023 1038,
  .cx 1038 1023,
  .cx 1039 1024,
  .cx 1024 1039,
  .cx 1039 1024,
  .cx 1040 1025,
  .cx 1025 1040]
private def block3482 : List Gate := [
  .cx 1040 1025,
  .cx 1041 1026,
  .cx 1026 1041,
  .cx 1041 1026,
  .cx 1042 1027,
  .cx 1027 1042,
  .cx 1042 1027,
  .cx 1598 1028,
  .cx 1028 1598,
  .cx 1598 1028,
  .cx 1557 1698,
  .cx 1698 1557,
  .cx 1557 1698,
  .cx 1558 1699,
  .cx 1699 1558,
  .cx 1558 1699,
  .cx 1708 1700,
  .cx 1700 1708,
  .cx 1708 1700,
  .cx 1706 1701,
  .cx 1701 1706,
  .cx 1706 1701,
  .cx 1710 1702,
  .cx 1702 1710,
  .cx 1710 1702,
  .cx 1709 1703,
  .cx 1703 1709,
  .cx 1709 1703]
private theorem check3482 : bitCheck block3482 0 = some 0 := by decide +kernel
private def suffix3482 := block3482 ++ ([]:List Gate)
private theorem valid3482 : bitCheck suffix3482 0 = some 0 := bit_join block3482 ([]:List Gate) _ 0 _ check3482 rfl
private theorem check3456 : bitCheck block3456 0 = some 0 := by decide +kernel
private def suffix3456 := block3456 ++ suffix3482
private theorem valid3456 : bitCheck suffix3456 0 = some 0 := bit_join block3456 suffix3482 _ 0 _ check3456 valid3482
private theorem check3442 : bitCheck block3442 0 = some 0 := by decide +kernel
private def suffix3442 := block3442 ++ suffix3456
private theorem valid3442 : bitCheck suffix3442 0 = some 0 := bit_join block3442 suffix3456 _ 0 _ check3442 valid3456
private theorem check3414 : bitCheck block3414 0 = some 0 := by decide +kernel
private def suffix3414 := block3414 ++ suffix3442
private theorem valid3414 : bitCheck suffix3414 0 = some 0 := bit_join block3414 suffix3442 _ 0 _ check3414 valid3442
private theorem check3402 : bitCheck block3402 0 = some 0 := by decide +kernel
private def suffix3402 := block3402 ++ suffix3414
private theorem valid3402 : bitCheck suffix3402 0 = some 0 := bit_join block3402 suffix3414 _ 0 _ check3402 valid3414
private theorem check3362 : bitCheck block3362 0 = some 0 := by decide +kernel
private def suffix3362 := block3362 ++ suffix3402
private theorem valid3362 : bitCheck suffix3362 0 = some 0 := bit_join block3362 suffix3402 _ 0 _ check3362 valid3402
private theorem check3360 : bitCheck block3360 0 = some 0 := by decide +kernel
private def suffix3360 := block3360 ++ suffix3362
private theorem valid3360 : bitCheck suffix3360 0 = some 0 := bit_join block3360 suffix3362 _ 0 _ check3360 valid3362
private theorem check3322 : bitCheck block3322 0 = some 0 := by decide +kernel
private def suffix3322 := block3322 ++ suffix3360
private theorem valid3322 : bitCheck suffix3322 0 = some 0 := bit_join block3322 suffix3360 _ 0 _ check3322 valid3360
private theorem check3318 : bitCheck block3318 0 = some 0 := by decide +kernel
private def suffix3318 := block3318 ++ suffix3322
private theorem valid3318 : bitCheck suffix3318 0 = some 0 := bit_join block3318 suffix3322 _ 0 _ check3318 valid3322
private theorem check3282 : bitCheck block3282 0 = some 0 := by decide +kernel
private def suffix3282 := block3282 ++ suffix3318
private theorem valid3282 : bitCheck suffix3282 0 = some 0 := bit_join block3282 suffix3318 _ 0 _ check3282 valid3318
private theorem check3264 : bitCheck block3264 0 = some 0 := by decide +kernel
private def suffix3264 := block3264 ++ suffix3282
private theorem valid3264 : bitCheck suffix3264 0 = some 0 := bit_join block3264 suffix3282 _ 0 _ check3264 valid3282
private theorem check3242 : bitCheck block3242 0 = some 0 := by decide +kernel
private def suffix3242 := block3242 ++ suffix3264
private theorem valid3242 : bitCheck suffix3242 0 = some 0 := bit_join block3242 suffix3264 _ 0 _ check3242 valid3264
private theorem check3222 : bitCheck block3222 0 = some 0 := by decide +kernel
private def suffix3222 := block3222 ++ suffix3242
private theorem valid3222 : bitCheck suffix3222 0 = some 0 := bit_join block3222 suffix3242 _ 0 _ check3222 valid3242
private theorem check3202 : bitCheck block3202 0 = some 0 := by decide +kernel
private def suffix3202 := block3202 ++ suffix3222
private theorem valid3202 : bitCheck suffix3202 0 = some 0 := bit_join block3202 suffix3222 _ 0 _ check3202 valid3222
private theorem check3168 : bitCheck block3168 0 = some (0x60 <<< 1556) := by decide +kernel
private def suffix3168 := block3168 ++ suffix3202
private theorem valid3168 : bitCheck suffix3168 0 = some (0x60 <<< 1556) := bit_join block3168 suffix3202 _ 0 _ check3168 valid3202
private theorem check3162 : bitCheck block3162 (0x60 <<< 1556) = some (0x79 <<< 1556) := by decide +kernel
private def suffix3162 := block3162 ++ suffix3168
private theorem valid3162 : bitCheck suffix3162 0 = some (0x79 <<< 1556) := bit_join block3162 suffix3168 _ (0x60 <<< 1556) _ check3162 valid3168
private def group2 := suffix3162
private theorem cert2 : bitCheck group2 0 = some (0x79 <<< 1556) := valid3162
private def block2515 : List Gate := [
  .ccx 1556 416 916,
  .ccx 1556 417 917,
  .ccx 1556 418 918,
  .ccx 1556 419 919,
  .ccx 1556 420 920,
  .ccx 1556 421 921,
  .ccx 1556 422 922,
  .ccx 1556 423 923,
  .ccx 1556 424 924,
  .ccx 1556 425 925,
  .x 916,
  .x 917,
  .x 918,
  .x 919,
  .x 920,
  .x 921,
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .make 916 1558 1559,
  .make 917 1559 1560,
  .make 918 1560 1561,
  .make 919 1561 1562,
  .make 920 1562 1563,
  .make 921 1563 1564,
  .make 922 1564 1565,
  .make 923 1565 1566,
  .make 924 1566 1567,
  .cx 1567 925,
  .pop 924 1566 1567,
  .cx 1566 924,
  .pop 923 1565 1566,
  .cx 1565 923,
  .pop 922 1564 1565]
private def block2550 : List Gate := [
  .cx 1564 922,
  .pop 921 1563 1564,
  .cx 1563 921,
  .pop 920 1562 1563,
  .cx 1562 920]
private def block2555 : List Gate := [
  .pop 919 1561 1562,
  .cx 1561 919,
  .pop 918 1560 1561,
  .cx 1560 918,
  .pop 917 1559 1560,
  .cx 1559 917,
  .pop 916 1558 1559,
  .cx 1558 916,
  .x 916,
  .x 917,
  .x 918,
  .x 919,
  .x 920,
  .x 921,
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .pop 915 1557 1558,
  .cx 415 1557,
  .x 1557,
  .make 423 424 1558,
  .x 1558,
  .x 425,
  .x 941,
  .x 942,
  .x 943,
  .x 944,
  .x 945,
  .x 946,
  .x 947,
  .x 948,
  .x 949,
  .x 950,
  .x 951,
  .x 952,
  .x 953]
private def block2592 : List Gate := [
  .x 954,
  .x 955,
  .x 956]
private def block2595 : List Gate := [
  .x 957,
  .x 958,
  .x 959,
  .x 960,
  .x 961,
  .x 962,
  .x 963,
  .x 964,
  .x 965,
  .x 966,
  .x 967,
  .x 968,
  .x 969,
  .x 970,
  .x 971,
  .x 972,
  .x 973,
  .x 974,
  .x 975,
  .x 976,
  .x 977,
  .x 978,
  .x 979,
  .x 980,
  .x 981,
  .x 982,
  .x 983,
  .x 984,
  .x 985,
  .x 986,
  .x 987,
  .x 988,
  .x 989,
  .x 990,
  .x 991,
  .x 992,
  .x 993,
  .x 994,
  .x 995,
  .x 996]
private def block2635 : List Gate := [
  .x 997,
  .x 998,
  .x 999,
  .x 1000,
  .x 1001,
  .x 1002,
  .x 1003,
  .x 1004,
  .x 1005,
  .x 1006,
  .x 1007]
private def block2646 : List Gate := [
  .x 1008,
  .x 1009,
  .x 1010,
  .x 1011,
  .x 1012,
  .x 1013,
  .x 1014,
  .x 1015,
  .x 1016,
  .x 1017,
  .x 1018,
  .x 1019,
  .x 1020,
  .x 1021,
  .x 1022,
  .x 1023,
  .x 1024,
  .x 1025,
  .x 1026,
  .x 1027,
  .x 1028,
  .x 1029,
  .x 1030,
  .x 1031,
  .x 1032,
  .x 1033,
  .x 1034,
  .x 1035,
  .x 1036]
private def block2675 : List Gate := [
  .x 1037,
  .x 1038,
  .x 1039,
  .x 1040,
  .x 1041,
  .x 1042,
  .x 1598,
  .x 1599,
  .x 1600,
  .x 1601,
  .x 1602,
  .x 1603,
  .x 1604]
private def block2688 : List Gate := [
  .x 1605,
  .x 1606,
  .x 1607,
  .x 1608,
  .x 1609,
  .x 1610,
  .x 1611,
  .x 1612,
  .make 1558 425 1559,
  .make 1559 941 1560,
  .make 1560 942 1561,
  .make 1561 943 1562,
  .make 1562 944 1563,
  .make 1563 945 1564,
  .make 1564 946 1565,
  .make 1565 947 1566,
  .make 1566 948 1567,
  .make 1567 949 1568,
  .make 1568 950 1569,
  .make 1569 951 1570,
  .make 1570 952 1571,
  .make 1571 953 1572,
  .make 1572 954 1573,
  .make 1573 955 1574,
  .make 1574 956 1575,
  .make 1575 957 1576,
  .make 1576 958 1577]
private def block2715 : List Gate := [
  .make 1577 959 1578,
  .make 1578 960 1579,
  .make 1579 961 1580,
  .make 1580 962 1581,
  .make 1581 963 1582,
  .make 1582 964 1583,
  .make 1583 965 1584,
  .make 1584 966 1585,
  .make 1585 967 1586,
  .make 1586 968 1587,
  .make 1587 969 1588,
  .make 1588 970 1589,
  .make 1589 971 1590,
  .make 1590 972 1591,
  .make 1591 973 1592,
  .make 1592 974 1593,
  .make 1593 975 1594,
  .make 1594 976 1595,
  .make 1595 977 1596,
  .make 1596 978 1597,
  .make 1597 979 1613,
  .make 1613 980 1614,
  .make 1614 981 1615,
  .make 1615 982 1616,
  .make 1616 983 1617,
  .make 1617 984 1618,
  .make 1618 985 1619]
private def block2742 : List Gate := [
  .make 1619 986 1620,
  .make 1620 987 1621,
  .make 1621 988 1622,
  .make 1622 989 1623,
  .make 1623 990 1624,
  .make 1624 991 1625,
  .make 1625 992 1626,
  .make 1626 993 1627,
  .make 1627 994 1628,
  .make 1628 995 1629,
  .make 1629 996 1630,
  .make 1630 997 1631,
  .make 1631 998 1632]
private def block2755 : List Gate := [
  .make 1632 999 1633,
  .make 1633 1000 1634,
  .make 1634 1001 1635,
  .make 1635 1002 1636,
  .make 1636 1003 1637,
  .make 1637 1004 1638,
  .make 1638 1005 1639,
  .make 1639 1006 1640,
  .make 1640 1007 1641,
  .make 1641 1008 1642,
  .make 1642 1009 1643,
  .make 1643 1010 1644,
  .make 1644 1011 1645,
  .make 1645 1012 1646,
  .make 1646 1013 1647,
  .make 1647 1014 1648,
  .make 1648 1015 1649,
  .make 1649 1016 1650,
  .make 1650 1017 1651,
  .make 1651 1018 1652,
  .make 1652 1019 1653,
  .make 1653 1020 1654,
  .make 1654 1021 1655,
  .make 1655 1022 1656,
  .make 1656 1023 1657,
  .make 1657 1024 1658,
  .make 1658 1025 1659,
  .make 1659 1026 1660,
  .make 1660 1027 1661]
private def block2784 : List Gate := [
  .make 1661 1028 1662,
  .make 1662 1029 1663,
  .make 1663 1030 1664,
  .make 1664 1031 1665,
  .make 1665 1032 1666,
  .make 1666 1033 1667,
  .make 1667 1034 1668,
  .make 1668 1035 1669,
  .make 1669 1036 1670,
  .make 1670 1037 1671,
  .make 1671 1038 1672]
private def block2795 : List Gate := [
  .make 1672 1039 1673,
  .make 1673 1040 1674,
  .make 1674 1041 1675,
  .make 1675 1042 1676,
  .make 1676 1598 1677,
  .make 1677 1599 1678,
  .make 1678 1600 1679,
  .make 1679 1601 1680,
  .make 1680 1602 1681,
  .make 1681 1603 1682,
  .make 1682 1604 1683,
  .make 1683 1605 1684,
  .make 1684 1606 1685,
  .make 1685 1607 1686,
  .make 1686 1608 1687,
  .make 1687 1609 1688,
  .make 1688 1610 1689,
  .make 1689 1611 1690,
  .make 1690 1612 1691,
  .cx 1691 1557,
  .x 1557,
  .pop 1690 1612 1691,
  .pop 1689 1611 1690,
  .pop 1688 1610 1689,
  .pop 1687 1609 1688,
  .pop 1686 1608 1687,
  .pop 1685 1607 1686,
  .pop 1684 1606 1685,
  .pop 1683 1605 1684,
  .pop 1682 1604 1683,
  .pop 1681 1603 1682,
  .pop 1680 1602 1681,
  .pop 1679 1601 1680,
  .pop 1678 1600 1679,
  .pop 1677 1599 1678,
  .pop 1676 1598 1677,
  .pop 1675 1042 1676,
  .pop 1674 1041 1675,
  .pop 1673 1040 1674,
  .pop 1672 1039 1673]
private def block2835 : List Gate := [
  .pop 1671 1038 1672,
  .pop 1670 1037 1671,
  .pop 1669 1036 1670]
private def block2838 : List Gate := [
  .pop 1668 1035 1669,
  .pop 1667 1034 1668,
  .pop 1666 1033 1667,
  .pop 1665 1032 1666,
  .pop 1664 1031 1665,
  .pop 1663 1030 1664,
  .pop 1662 1029 1663,
  .pop 1661 1028 1662,
  .pop 1660 1027 1661,
  .pop 1659 1026 1660,
  .pop 1658 1025 1659,
  .pop 1657 1024 1658,
  .pop 1656 1023 1657,
  .pop 1655 1022 1656,
  .pop 1654 1021 1655,
  .pop 1653 1020 1654,
  .pop 1652 1019 1653,
  .pop 1651 1018 1652,
  .pop 1650 1017 1651,
  .pop 1649 1016 1650,
  .pop 1648 1015 1649,
  .pop 1647 1014 1648,
  .pop 1646 1013 1647,
  .pop 1645 1012 1646,
  .pop 1644 1011 1645,
  .pop 1643 1010 1644,
  .pop 1642 1009 1643,
  .pop 1641 1008 1642,
  .pop 1640 1007 1641,
  .pop 1639 1006 1640,
  .pop 1638 1005 1639,
  .pop 1637 1004 1638,
  .pop 1636 1003 1637,
  .pop 1635 1002 1636,
  .pop 1634 1001 1635,
  .pop 1633 1000 1634,
  .pop 1632 999 1633]
private def block2875 : List Gate := [
  .pop 1631 998 1632,
  .pop 1630 997 1631,
  .pop 1629 996 1630,
  .pop 1628 995 1629,
  .pop 1627 994 1628]
private def block2880 : List Gate := [
  .pop 1626 993 1627,
  .pop 1625 992 1626,
  .pop 1624 991 1625,
  .pop 1623 990 1624,
  .pop 1622 989 1623,
  .pop 1621 988 1622,
  .pop 1620 987 1621,
  .pop 1619 986 1620,
  .pop 1618 985 1619,
  .pop 1617 984 1618,
  .pop 1616 983 1617,
  .pop 1615 982 1616,
  .pop 1614 981 1615,
  .pop 1613 980 1614,
  .pop 1597 979 1613,
  .pop 1596 978 1597,
  .pop 1595 977 1596,
  .pop 1594 976 1595,
  .pop 1593 975 1594,
  .pop 1592 974 1593,
  .pop 1591 973 1592,
  .pop 1590 972 1591,
  .pop 1589 971 1590,
  .pop 1588 970 1589,
  .pop 1587 969 1588,
  .pop 1586 968 1587,
  .pop 1585 967 1586,
  .pop 1584 966 1585,
  .pop 1583 965 1584,
  .pop 1582 964 1583,
  .pop 1581 963 1582,
  .pop 1580 962 1581,
  .pop 1579 961 1580,
  .pop 1578 960 1579,
  .pop 1577 959 1578]
private def block2915 : List Gate := [
  .pop 1576 958 1577,
  .pop 1575 957 1576,
  .pop 1574 956 1575,
  .pop 1573 955 1574,
  .pop 1572 954 1573,
  .pop 1571 953 1572,
  .pop 1570 952 1571,
  .pop 1569 951 1570,
  .pop 1568 950 1569,
  .pop 1567 949 1568,
  .pop 1566 948 1567,
  .pop 1565 947 1566,
  .pop 1564 946 1565,
  .pop 1563 945 1564,
  .pop 1562 944 1563,
  .pop 1561 943 1562,
  .pop 1560 942 1561,
  .pop 1559 941 1560,
  .pop 1558 425 1559]
private def block2934 : List Gate := [
  .x 1612,
  .x 1611,
  .x 1610,
  .x 1609,
  .x 1608,
  .x 1607,
  .x 1606,
  .x 1605,
  .x 1604,
  .x 1603,
  .x 1602,
  .x 1601,
  .x 1600,
  .x 1599,
  .x 1598,
  .x 1042,
  .x 1041,
  .x 1040,
  .x 1039,
  .x 1038,
  .x 1037]
private def block2955 : List Gate := [
  .x 1036,
  .x 1035,
  .x 1034,
  .x 1033,
  .x 1032,
  .x 1031,
  .x 1030,
  .x 1029,
  .x 1028,
  .x 1027,
  .x 1026,
  .x 1025,
  .x 1024,
  .x 1023,
  .x 1022,
  .x 1021,
  .x 1020,
  .x 1019,
  .x 1018,
  .x 1017,
  .x 1016]
private def block2976 : List Gate := [
  .x 1015,
  .x 1014,
  .x 1013,
  .x 1012,
  .x 1011,
  .x 1010,
  .x 1009,
  .x 1008,
  .x 1007,
  .x 1006,
  .x 1005,
  .x 1004,
  .x 1003,
  .x 1002,
  .x 1001,
  .x 1000,
  .x 999,
  .x 998,
  .x 997]
private def block2995 : List Gate := [
  .x 996,
  .x 995,
  .x 994,
  .x 993,
  .x 992,
  .x 991,
  .x 990,
  .x 989,
  .x 988,
  .x 987,
  .x 986,
  .x 985,
  .x 984,
  .x 983,
  .x 982,
  .x 981,
  .x 980,
  .x 979,
  .x 978,
  .x 977,
  .x 976,
  .x 975,
  .x 974,
  .x 973,
  .x 972,
  .x 971,
  .x 970,
  .x 969,
  .x 968,
  .x 967,
  .x 966,
  .x 965,
  .x 964,
  .x 963,
  .x 962]
private def block3030 : List Gate := [
  .x 961,
  .x 960,
  .x 959,
  .x 958,
  .x 957]
private def block3035 : List Gate := [
  .x 956,
  .x 955,
  .x 954,
  .x 953,
  .x 952,
  .x 951,
  .x 950,
  .x 949,
  .x 948,
  .x 947,
  .x 946,
  .x 945,
  .x 944,
  .x 943,
  .x 942,
  .x 941,
  .x 425,
  .x 1558,
  .pop 423 424 1558,
  .make 1556 1557 1558,
  .x 1558,
  .x 915,
  .x 916,
  .x 917,
  .x 918,
  .x 919,
  .x 920,
  .x 921,
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .make 1558 915 1559,
  .make 1559 916 1560,
  .make 1560 917 1561,
  .make 1561 918 1562,
  .make 1562 919 1563]
private def block3072 : List Gate := [
  .make 1563 920 1564,
  .make 1564 921 1565,
  .make 1565 922 1566]
private def block3075 : List Gate := [
  .make 1566 923 1567,
  .make 1567 924 1568,
  .make 1568 925 1569,
  .cx 1569 1556,
  .x 1556,
  .pop 1568 925 1569,
  .pop 1567 924 1568,
  .pop 1566 923 1567,
  .pop 1565 922 1566,
  .pop 1564 921 1565,
  .pop 1563 920 1564,
  .pop 1562 919 1563,
  .pop 1561 918 1562,
  .pop 1560 917 1561,
  .pop 1559 916 1560,
  .pop 1558 915 1559,
  .x 925,
  .x 924,
  .x 923,
  .x 922,
  .x 921,
  .x 920,
  .x 919,
  .x 918,
  .x 917,
  .x 916,
  .x 915,
  .x 1558,
  .x 271,
  .x 272,
  .x 273,
  .x 274,
  .x 275,
  .x 276,
  .x 277,
  .x 278,
  .x 279,
  .x 280,
  .x 281,
  .x 282]
private def block3115 : List Gate := [
  .x 283,
  .x 284,
  .x 285,
  .cx 1708 915,
  .cx 1708 916,
  .cx 1708 917,
  .cx 1708 918,
  .cx 1708 919,
  .cx 1708 920,
  .cx 1708 921,
  .cx 1708 922]
private def block3126 : List Gate := [
  .cx 1708 923,
  .cx 1708 924,
  .cx 1708 925,
  .cx 415 915,
  .ccx 285 915 415,
  .cx 415 915,
  .cx 416 916,
  .ccx 285 916 416,
  .cx 416 916,
  .cx 417 917,
  .ccx 285 917 417,
  .cx 417 917,
  .cx 418 918,
  .ccx 285 918 418,
  .cx 418 918,
  .cx 419 919,
  .ccx 285 919 419,
  .cx 419 919,
  .cx 420 920,
  .ccx 285 920 420,
  .cx 420 920,
  .cx 421 921,
  .ccx 285 921 421,
  .cx 421 921,
  .cx 422 922,
  .ccx 285 922 422,
  .cx 422 922,
  .cx 423 923,
  .ccx 285 923 423]
private def block3155 : List Gate := [
  .cx 423 923,
  .cx 424 924,
  .ccx 285 924 424,
  .cx 424 924,
  .cx 425 925,
  .ccx 285 925 425,
  .cx 425 925]
private theorem check3155 : bitCheck block3155 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix3155 := block3155 ++ ([]:List Gate)
private theorem valid3155 : bitCheck suffix3155 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block3155 ([]:List Gate) _ (0x78 <<< 1556) _ check3155 rfl
private theorem check3126 : bitCheck block3126 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix3126 := block3126 ++ suffix3155
private theorem valid3126 : bitCheck suffix3126 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block3126 suffix3155 _ (0x78 <<< 1556) _ check3126 valid3155
private theorem check3115 : bitCheck block3115 (0x78 <<< 1556) = some (0x78 <<< 1556) := by decide +kernel
private def suffix3115 := block3115 ++ suffix3126
private theorem valid3115 : bitCheck suffix3115 (0x78 <<< 1556) = some (0x78 <<< 1556) := bit_join block3115 suffix3126 _ (0x78 <<< 1556) _ check3115 valid3126
private theorem check3075 : bitCheck block3075 (0x78 <<< 1556) = some (0x3800 <<< 1556) := by decide +kernel
private def suffix3075 := block3075 ++ suffix3115
private theorem valid3075 : bitCheck suffix3075 (0x78 <<< 1556) = some (0x3800 <<< 1556) := bit_join block3075 suffix3115 _ (0x78 <<< 1556) _ check3075 valid3115
private theorem check3072 : bitCheck block3072 (0x3800 <<< 1556) = some (0x3f00 <<< 1556) := by decide +kernel
private def suffix3072 := block3072 ++ suffix3075
private theorem valid3072 : bitCheck suffix3072 (0x78 <<< 1556) = some (0x3f00 <<< 1556) := bit_join block3072 suffix3075 _ (0x3800 <<< 1556) _ check3072 valid3075
private theorem check3035 : bitCheck block3035 (0x3f00 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix3035 := block3035 ++ suffix3072
private theorem valid3035 : bitCheck suffix3035 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block3035 suffix3072 _ (0x3f00 <<< 1556) _ check3035 valid3072
private theorem check3030 : bitCheck block3030 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix3030 := block3030 ++ suffix3035
private theorem valid3030 : bitCheck suffix3030 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block3030 suffix3035 _ (0x3ff8 <<< 1556) _ check3030 valid3035
private theorem check2995 : bitCheck block2995 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2995 := block2995 ++ suffix3030
private theorem valid2995 : bitCheck suffix2995 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2995 suffix3030 _ (0x3ff8 <<< 1556) _ check2995 valid3030
private theorem check2976 : bitCheck block2976 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2976 := block2976 ++ suffix2995
private theorem valid2976 : bitCheck suffix2976 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2976 suffix2995 _ (0x3ff8 <<< 1556) _ check2976 valid2995
private theorem check2955 : bitCheck block2955 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2955 := block2955 ++ suffix2976
private theorem valid2955 : bitCheck suffix2955 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2955 suffix2976 _ (0x3ff8 <<< 1556) _ check2955 valid2976
private theorem check2934 : bitCheck block2934 (0x3ff8 <<< 1556) = some (0x3ff8 <<< 1556) := by decide +kernel
private def suffix2934 := block2934 ++ suffix2955
private theorem valid2934 : bitCheck suffix2934 (0x78 <<< 1556) = some (0x3ff8 <<< 1556) := bit_join block2934 suffix2955 _ (0x3ff8 <<< 1556) _ check2934 valid2955
private theorem check2915 : bitCheck block2915 (0x3ff8 <<< 1556) = some 0 := by decide +kernel
private def suffix2915 := block2915 ++ suffix2934
private theorem valid2915 : bitCheck suffix2915 (0x78 <<< 1556) = some 0 := bit_join block2915 suffix2934 _ (0x3ff8 <<< 1556) _ check2915 valid2934
private theorem check2880 : bitCheck block2880 0 = some 0 := by decide +kernel
private def suffix2880 := block2880 ++ suffix2915
private theorem valid2880 : bitCheck suffix2880 (0x78 <<< 1556) = some 0 := bit_join block2880 suffix2915 _ 0 _ check2880 valid2915
private theorem check2875 : bitCheck block2875 0 = some 0 := by decide +kernel
private def suffix2875 := block2875 ++ suffix2880
private theorem valid2875 : bitCheck suffix2875 (0x78 <<< 1556) = some 0 := bit_join block2875 suffix2880 _ 0 _ check2875 valid2880
private theorem check2838 : bitCheck block2838 0 = some 0 := by decide +kernel
private def suffix2838 := block2838 ++ suffix2875
private theorem valid2838 : bitCheck suffix2838 (0x78 <<< 1556) = some 0 := bit_join block2838 suffix2875 _ 0 _ check2838 valid2875
private theorem check2835 : bitCheck block2835 0 = some 0 := by decide +kernel
private def suffix2835 := block2835 ++ suffix2838
private theorem valid2835 : bitCheck suffix2835 (0x78 <<< 1556) = some 0 := bit_join block2835 suffix2838 _ 0 _ check2835 valid2838
private theorem check2795 : bitCheck block2795 0 = some (0xffffe00000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2795 := block2795 ++ suffix2835
private theorem valid2795 : bitCheck suffix2795 (0x78 <<< 1556) = some (0xffffe00000000000000000000000000000 <<< 1556) := bit_join block2795 suffix2835 _ 0 _ check2795 valid2835
private theorem check2784 : bitCheck block2784 (0xffffe00000000000000000000000000000 <<< 1556) = some (0xfffffffc00000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix2784 := block2784 ++ suffix2795
private theorem valid2784 : bitCheck suffix2784 (0x78 <<< 1556) = some (0xfffffffc00000000000000000000000000 <<< 1556) := bit_join block2784 suffix2795 _ (0xffffe00000000000000000000000000000 <<< 1556) _ check2784 valid2795
private theorem check2755 : bitCheck block2755 (0xfffffffc00000000000000000000000000 <<< 1556) = some (0xffffffffffffffe0000000000000000000 <<< 1556) := by decide +kernel
private def suffix2755 := block2755 ++ suffix2784
private theorem valid2755 : bitCheck suffix2755 (0x78 <<< 1556) = some (0xffffffffffffffe0000000000000000000 <<< 1556) := bit_join block2755 suffix2784 _ (0xfffffffc00000000000000000000000000 <<< 1556) _ check2755 valid2784
private theorem check2742 : bitCheck block2742 (0xffffffffffffffe0000000000000000000 <<< 1556) = some (0xffffffffffffffffff0000000000000000 <<< 1556) := by decide +kernel
private def suffix2742 := block2742 ++ suffix2755
private theorem valid2742 : bitCheck suffix2742 (0x78 <<< 1556) = some (0xffffffffffffffffff0000000000000000 <<< 1556) := bit_join block2742 suffix2755 _ (0xffffffffffffffe0000000000000000000 <<< 1556) _ check2742 valid2755
private theorem check2715 : bitCheck block2715 (0xffffffffffffffffff0000000000000000 <<< 1556) = some (0xfffffffffffffffffffe0003ffffc00000 <<< 1556) := by decide +kernel
private def suffix2715 := block2715 ++ suffix2742
private theorem valid2715 : bitCheck suffix2715 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003ffffc00000 <<< 1556) := bit_join block2715 suffix2742 _ (0xffffffffffffffffff0000000000000000 <<< 1556) _ check2715 valid2742
private theorem check2688 : bitCheck block2688 (0xfffffffffffffffffffe0003ffffc00000 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2688 := block2688 ++ suffix2715
private theorem valid2688 : bitCheck suffix2688 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2688 suffix2715 _ (0xfffffffffffffffffffe0003ffffc00000 <<< 1556) _ check2688 valid2715
private theorem check2675 : bitCheck block2675 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2675 := block2675 ++ suffix2688
private theorem valid2675 : bitCheck suffix2675 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2675 suffix2688 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2675 valid2688
private theorem check2646 : bitCheck block2646 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2646 := block2646 ++ suffix2675
private theorem valid2646 : bitCheck suffix2646 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2646 suffix2675 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2646 valid2675
private theorem check2635 : bitCheck block2635 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2635 := block2635 ++ suffix2646
private theorem valid2635 : bitCheck suffix2635 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2635 suffix2646 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2635 valid2646
private theorem check2595 : bitCheck block2595 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2595 := block2595 ++ suffix2635
private theorem valid2595 : bitCheck suffix2595 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2595 suffix2635 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2595 valid2635
private theorem check2592 : bitCheck block2592 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2592 := block2592 ++ suffix2595
private theorem valid2592 : bitCheck suffix2592 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2592 suffix2595 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2592 valid2595
private theorem check2555 : bitCheck block2555 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) = some (0xfffffffffffffffffffe0003ffffffff80 <<< 1556) := by decide +kernel
private def suffix2555 := block2555 ++ suffix2592
private theorem valid2555 : bitCheck suffix2555 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003ffffffff80 <<< 1556) := bit_join block2555 suffix2592 _ (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) _ check2555 valid2592
private theorem check2550 : bitCheck block2550 (0xfffffffffffffffffffe0003ffffffff80 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffe00 <<< 1556) := by decide +kernel
private def suffix2550 := block2550 ++ suffix2555
private theorem valid2550 : bitCheck suffix2550 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffe00 <<< 1556) := bit_join block2550 suffix2555 _ (0xfffffffffffffffffffe0003ffffffff80 <<< 1556) _ check2550 valid2555
private theorem check2515 : bitCheck block2515 (0xfffffffffffffffffffe0003fffffffe00 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := by decide +kernel
private def suffix2515 := block2515 ++ suffix2550
private theorem valid2515 : bitCheck suffix2515 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := bit_join block2515 suffix2550 _ (0xfffffffffffffffffffe0003fffffffe00 <<< 1556) _ check2515 valid2550
private def group1 := suffix2515
private theorem cert1 : bitCheck group1 (0x78 <<< 1556) = some (0xfffffffffffffffffffe0003fffffffff8 <<< 1556) := valid2515
private def block0 : List Gate := [
  .cx 433 1708,
  .cx 933 1708,
  .cx 415 915,
  .ccx 285 915 415,
  .cx 415 915,
  .cx 416 916,
  .ccx 285 916 416,
  .cx 416 916,
  .cx 417 917,
  .ccx 285 917 417,
  .cx 417 917,
  .cx 418 918,
  .ccx 285 918 418,
  .cx 418 918,
  .cx 419 919,
  .ccx 285 919 419,
  .cx 419 919,
  .cx 420 920,
  .ccx 285 920 420,
  .cx 420 920,
  .cx 421 921,
  .ccx 285 921 421,
  .cx 421 921,
  .cx 422 922,
  .ccx 285 922 422,
  .cx 422 922,
  .cx 423 923,
  .ccx 285 923 423,
  .cx 423 923,
  .cx 424 924,
  .ccx 285 924 424,
  .cx 424 924,
  .cx 425 925,
  .ccx 285 925 425,
  .cx 425 925,
  .cx 426 926,
  .ccx 285 926 426,
  .cx 426 926,
  .cx 427 927,
  .ccx 285 927 427]
private def block40 : List Gate := [
  .cx 427 927,
  .cx 428 928,
  .ccx 285 928 428,
  .cx 428 928,
  .cx 429 929,
  .ccx 285 929 429,
  .cx 429 929,
  .cx 430 930,
  .ccx 285 930 430,
  .cx 430 930,
  .cx 431 931,
  .ccx 285 931 431,
  .cx 431 931,
  .cx 432 932]
private def block54 : List Gate := [
  .ccx 285 932 432,
  .cx 432 932,
  .cx 433 933,
  .ccx 285 933 433,
  .cx 433 933,
  .cx 1708 915,
  .cx 1708 916,
  .cx 1708 917,
  .cx 1708 918,
  .cx 1708 919,
  .cx 1708 920,
  .cx 1708 921,
  .cx 1708 922,
  .cx 1708 923,
  .cx 1708 924,
  .cx 1708 925,
  .cx 1708 926,
  .cx 1708 927,
  .cx 1708 928,
  .cx 1708 929,
  .cx 1708 930,
  .cx 1708 931,
  .cx 1708 932,
  .cx 1708 933,
  .x 271,
  .x 272]
private def block80 : List Gate := [
  .x 273,
  .x 274,
  .x 275,
  .x 276,
  .x 277,
  .x 278,
  .x 279,
  .x 280,
  .x 281,
  .x 282,
  .x 283,
  .x 284,
  .x 285,
  .x 915,
  .x 916,
  .x 917]
private def block96 : List Gate := [
  .x 918,
  .x 919,
  .x 920,
  .x 921,
  .x 922,
  .x 923,
  .x 924,
  .x 925,
  .x 926,
  .x 927,
  .x 928,
  .x 929,
  .x 930,
  .x 931,
  .x 932,
  .x 933,
  .make 915 916 1557,
  .make 1557 917 1558,
  .make 1558 918 1559,
  .make 1559 919 1560,
  .make 1560 920 1561,
  .make 1561 921 1562,
  .make 1562 922 1563,
  .make 1563 923 1564]
private def block120 : List Gate := [
  .make 1564 924 1565,
  .make 1565 925 1566,
  .make 1566 926 1567,
  .make 1567 927 1568,
  .make 1568 928 1569,
  .make 1569 929 1570,
  .make 1570 930 1571,
  .make 1571 931 1572,
  .make 1572 932 1573,
  .make 1573 933 1574,
  .cx 1574 1556,
  .x 1556,
  .pop 1573 933 1574,
  .pop 1572 932 1573,
  .pop 1571 931 1572,
  .pop 1570 930 1571,
  .pop 1569 929 1570,
  .pop 1568 928 1569,
  .pop 1567 927 1568,
  .pop 1566 926 1567,
  .pop 1565 925 1566,
  .pop 1564 924 1565,
  .pop 1563 923 1564,
  .pop 1562 922 1563,
  .pop 1561 921 1562,
  .pop 1560 920 1561,
  .pop 1559 919 1560,
  .pop 1558 918 1559,
  .pop 1557 917 1558,
  .pop 915 916 1557]
private def block150 : List Gate := [
  .x 933,
  .x 932,
  .x 931,
  .x 930,
  .x 929,
  .x 928,
  .x 927,
  .x 926,
  .x 925,
  .x 924]
private def block160 : List Gate := [
  .x 923,
  .x 922,
  .x 921,
  .x 920,
  .x 919,
  .x 918,
  .x 917,
  .x 916,
  .x 915,
  .x 1557,
  .cx 415 1557,
  .make 915 1557 1558,
  .make 916 1558 1559,
  .make 917 1559 1560,
  .make 918 1560 1561,
  .make 919 1561 1562,
  .make 920 1562 1563,
  .make 921 1563 1564,
  .make 922 1564 1565,
  .make 923 1565 1566,
  .make 924 1566 1567,
  .make 925 1567 1568,
  .make 926 1568 1569,
  .make 927 1569 1570,
  .make 928 1570 1571,
  .make 929 1571 1572,
  .make 930 1572 1573,
  .make 931 1573 1574,
  .make 932 1574 1575,
  .cx 1575 933,
  .pop 932 1574 1575,
  .cx 1574 932]
private def block192 : List Gate := [
  .pop 931 1573 1574,
  .cx 1573 931,
  .pop 930 1572 1573,
  .cx 1572 930,
  .pop 929 1571 1572,
  .cx 1571 929,
  .pop 928 1570 1571,
  .cx 1570 928]
private def block200 : List Gate := [
  .pop 927 1569 1570,
  .cx 1569 927,
  .pop 926 1568 1569,
  .cx 1568 926,
  .pop 925 1567 1568,
  .cx 1567 925,
  .pop 924 1566 1567,
  .cx 1566 924,
  .pop 923 1565 1566,
  .cx 1565 923,
  .pop 922 1564 1565,
  .cx 1564 922,
  .pop 921 1563 1564,
  .cx 1563 921,
  .pop 920 1562 1563,
  .cx 1562 920,
  .pop 919 1561 1562,
  .cx 1561 919,
  .pop 918 1560 1561,
  .cx 1560 918,
  .pop 917 1559 1560,
  .cx 1559 917,
  .pop 916 1558 1559,
  .cx 1558 916,
  .ccx 1556 416 916,
  .ccx 1556 417 917,
  .ccx 1556 418 918,
  .ccx 1556 419 919,
  .ccx 1556 420 920,
  .ccx 1556 421 921,
  .ccx 1556 422 922,
  .ccx 1556 423 923,
  .ccx 1556 424 924,
  .ccx 1556 425 925,
  .ccx 1556 426 926,
  .ccx 1556 427 927,
  .ccx 1556 428 928,
  .ccx 1556 429 929,
  .ccx 1556 430 930,
  .ccx 1556 431 931]
private def block240 : List Gate := [
  .ccx 1556 432 932,
  .ccx 1556 433 933,
  .make 1706 1707 1559,
  .cx 1706 1560,
  .cx 1559 1560,
  .make 1560 1299 1561]
private def block246 : List Gate := [
  .cx 1561 1560,
  .make 1560 1300 1562,
  .cx 1562 1560,
  .make 1560 1812 1563,
  .cx 1563 1560,
  .make 1560 1811 1564,
  .cx 1564 1560,
  .make 1560 1810 1565,
  .cx 1565 1560,
  .make 1560 1809 1566,
  .cx 1566 1560,
  .make 1560 1808 1567,
  .cx 1567 1560,
  .make 1560 1807 1568,
  .cx 1568 1560,
  .make 1560 1806 1569,
  .cx 1569 1560,
  .make 1560 1805 1570,
  .cx 1570 1560,
  .make 1560 1804 1571,
  .cx 1571 1560,
  .make 1560 1803 1572,
  .cx 1572 1560,
  .make 1560 1802 1573,
  .cx 1573 1560,
  .make 1560 1801 1574,
  .cx 1574 1560,
  .make 1560 1800 1575,
  .cx 1575 1560,
  .cx 1559 1710,
  .cx 1561 1710,
  .cx 1562 1710,
  .cx 1563 1710,
  .cx 1564 1710]
private def block280 : List Gate := [
  .cx 1565 1710,
  .cx 1559 1576,
  .cx 1561 1576,
  .make 284 285 1577,
  .make 283 1577 1578,
  .make 282 1578 1579,
  .make 281 1579 1580,
  .make 280 1580 1581]
private def block288 : List Gate := [
  .make 279 1581 1582,
  .make 278 1582 1583,
  .make 277 1583 1584,
  .make 276 1584 1585,
  .make 275 1585 1586,
  .make 274 1586 1587,
  .make 273 1587 1588,
  .make 1562 1588 1589,
  .make 1563 1586 1590,
  .make 1564 1584 1591,
  .make 1565 1582 1592,
  .make 1566 1580 1593,
  .make 1567 1578 1594,
  .make 1568 285 1595,
  .ccx 1576 416 1709,
  .ccx 1562 417 1709,
  .ccx 1563 418 1709,
  .ccx 1564 419 1709,
  .ccx 1565 420 1709,
  .ccx 1566 421 1709,
  .ccx 1567 422 1709,
  .ccx 1568 423 1709,
  .ccx 1569 424 1709,
  .ccx 1570 425 1709,
  .ccx 1571 426 1709,
  .ccx 1572 427 1709,
  .ccx 1573 428 1709,
  .ccx 1574 429 1709,
  .ccx 1575 430 1709,
  .ccx 1560 431 1709,
  .cx 1589 1596,
  .cx 1590 1596]
private def block320 : List Gate := [
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596,
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .make 1709 1596 1597,
  .cx 1597 1703,
  .cx 1597 1704,
  .cx 1597 1705,
  .cx 1597 934,
  .cx 1597 935,
  .cx 1597 936,
  .cx 1597 937,
  .cx 1597 938]
private def block342 : List Gate := [
  .cx 1597 939,
  .cx 1597 940,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943,
  .cx 1597 944,
  .cx 1597 945,
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950,
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956]
private def block360 : List Gate := [
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972,
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980]
private def block384 : List Gate := [
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990,
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996]
private def block400 : List Gate := [
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014,
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030,
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034]
private def block438 : List Gate := [
  .cx 1597 1035,
  .cx 1597 1036]
private def block440 : List Gate := [
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .make 1703 1709 1598,
  .make 1704 1598 1599,
  .make 1705 1599 1600,
  .make 934 1600 1601,
  .make 935 1601 1602,
  .make 936 1602 1603,
  .make 937 1603 1604,
  .make 938 1604 1605,
  .make 939 1605 1606,
  .make 940 1606 1607,
  .make 941 1607 1608,
  .make 942 1608 1609,
  .make 943 1609 1610,
  .make 944 1610 1611,
  .make 945 1611 1612,
  .make 946 1612 1613,
  .make 947 1613 1614,
  .make 948 1614 1615,
  .make 949 1615 1616,
  .make 950 1616 1617,
  .make 951 1617 1618,
  .make 952 1618 1619,
  .make 953 1619 1620,
  .make 954 1620 1621,
  .make 955 1621 1622,
  .make 956 1622 1623,
  .make 957 1623 1624,
  .make 958 1624 1625,
  .make 959 1625 1626,
  .make 960 1626 1627,
  .make 961 1627 1628,
  .make 962 1628 1629,
  .make 963 1629 1630,
  .make 964 1630 1631]
private def block480 : List Gate := [
  .make 965 1631 1632,
  .make 966 1632 1633,
  .make 967 1633 1634,
  .make 968 1634 1635,
  .make 969 1635 1636,
  .make 970 1636 1637,
  .make 971 1637 1638,
  .make 972 1638 1639,
  .make 973 1639 1640,
  .make 974 1640 1641,
  .make 975 1641 1642,
  .make 976 1642 1643,
  .make 977 1643 1644,
  .make 978 1644 1645,
  .make 979 1645 1646,
  .make 980 1646 1647,
  .make 981 1647 1648,
  .make 982 1648 1649,
  .make 983 1649 1650,
  .make 984 1650 1651,
  .make 985 1651 1652,
  .make 986 1652 1653,
  .make 987 1653 1654,
  .make 988 1654 1655,
  .make 989 1655 1656,
  .make 990 1656 1657,
  .make 991 1657 1658,
  .make 992 1658 1659,
  .make 993 1659 1660,
  .make 994 1660 1661,
  .make 995 1661 1662,
  .make 996 1662 1663,
  .make 997 1663 1664,
  .make 998 1664 1665,
  .make 999 1665 1666,
  .make 1000 1666 1667,
  .make 1001 1667 1668,
  .make 1002 1668 1669,
  .make 1003 1669 1670,
  .make 1004 1670 1671]
private def block520 : List Gate := [
  .make 1005 1671 1672,
  .make 1006 1672 1673,
  .make 1007 1673 1674,
  .make 1008 1674 1675,
  .make 1009 1675 1676,
  .make 1010 1676 1677,
  .make 1011 1677 1678,
  .make 1012 1678 1679,
  .make 1013 1679 1680,
  .make 1014 1680 1681,
  .make 1015 1681 1682,
  .make 1016 1682 1683,
  .make 1017 1683 1684,
  .make 1018 1684 1685]
private def block534 : List Gate := [
  .make 1019 1685 1686,
  .make 1020 1686 1687,
  .make 1021 1687 1688,
  .make 1022 1688 1689,
  .make 1023 1689 1690,
  .make 1024 1690 1691,
  .make 1025 1691 1692,
  .make 1026 1692 1693,
  .make 1027 1693 1694,
  .make 1028 1694 1695,
  .make 1029 1695 1696,
  .make 1030 1696 1697,
  .make 1031 1697 1698,
  .make 1032 1698 1699,
  .make 1033 1699 1700,
  .make 1034 1700 1701,
  .make 1035 1701 1702,
  .make 1036 1702 1713,
  .make 1037 1713 1714,
  .make 1038 1714 1715,
  .make 1039 1715 1716,
  .make 1040 1716 1717,
  .make 1041 1717 1718,
  .cx 1718 1042,
  .pop 1041 1717 1718,
  .cx 1717 1041]
private def block560 : List Gate := [
  .pop 1040 1716 1717,
  .cx 1716 1040,
  .pop 1039 1715 1716,
  .cx 1715 1039,
  .pop 1038 1714 1715,
  .cx 1714 1038,
  .pop 1037 1713 1714,
  .cx 1713 1037,
  .pop 1036 1702 1713,
  .cx 1702 1036,
  .pop 1035 1701 1702,
  .cx 1701 1035,
  .pop 1034 1700 1701,
  .cx 1700 1034,
  .pop 1033 1699 1700,
  .cx 1699 1033]
private def block576 : List Gate := [
  .pop 1032 1698 1699,
  .cx 1698 1032,
  .pop 1031 1697 1698,
  .cx 1697 1031,
  .pop 1030 1696 1697,
  .cx 1696 1030,
  .pop 1029 1695 1696,
  .cx 1695 1029,
  .pop 1028 1694 1695,
  .cx 1694 1028,
  .pop 1027 1693 1694,
  .cx 1693 1027,
  .pop 1026 1692 1693,
  .cx 1692 1026,
  .pop 1025 1691 1692,
  .cx 1691 1025,
  .pop 1024 1690 1691,
  .cx 1690 1024,
  .pop 1023 1689 1690,
  .cx 1689 1023,
  .pop 1022 1688 1689,
  .cx 1688 1022,
  .pop 1021 1687 1688,
  .cx 1687 1021]
private def block600 : List Gate := [
  .pop 1020 1686 1687,
  .cx 1686 1020,
  .pop 1019 1685 1686,
  .cx 1685 1019,
  .pop 1018 1684 1685,
  .cx 1684 1018,
  .pop 1017 1683 1684,
  .cx 1683 1017,
  .pop 1016 1682 1683,
  .cx 1682 1016,
  .pop 1015 1681 1682,
  .cx 1681 1015,
  .pop 1014 1680 1681,
  .cx 1680 1014,
  .pop 1013 1679 1680,
  .cx 1679 1013,
  .pop 1012 1678 1679,
  .cx 1678 1012,
  .pop 1011 1677 1678,
  .cx 1677 1011,
  .pop 1010 1676 1677,
  .cx 1676 1010,
  .pop 1009 1675 1676,
  .cx 1675 1009,
  .pop 1008 1674 1675,
  .cx 1674 1008,
  .pop 1007 1673 1674,
  .cx 1673 1007,
  .pop 1006 1672 1673,
  .cx 1672 1006]
private def block630 : List Gate := [
  .pop 1005 1671 1672,
  .cx 1671 1005,
  .pop 1004 1670 1671,
  .cx 1670 1004,
  .pop 1003 1669 1670,
  .cx 1669 1003,
  .pop 1002 1668 1669,
  .cx 1668 1002,
  .pop 1001 1667 1668,
  .cx 1667 1001]
private def block640 : List Gate := [
  .pop 1000 1666 1667,
  .cx 1666 1000,
  .pop 999 1665 1666,
  .cx 1665 999,
  .pop 998 1664 1665,
  .cx 1664 998,
  .pop 997 1663 1664,
  .cx 1663 997,
  .pop 996 1662 1663,
  .cx 1662 996,
  .pop 995 1661 1662,
  .cx 1661 995,
  .pop 994 1660 1661,
  .cx 1660 994,
  .pop 993 1659 1660,
  .cx 1659 993,
  .pop 992 1658 1659,
  .cx 1658 992,
  .pop 991 1657 1658,
  .cx 1657 991,
  .pop 990 1656 1657,
  .cx 1656 990,
  .pop 989 1655 1656,
  .cx 1655 989,
  .pop 988 1654 1655,
  .cx 1654 988,
  .pop 987 1653 1654,
  .cx 1653 987,
  .pop 986 1652 1653,
  .cx 1652 986,
  .pop 985 1651 1652,
  .cx 1651 985]
private def block672 : List Gate := [
  .pop 984 1650 1651,
  .cx 1650 984,
  .pop 983 1649 1650,
  .cx 1649 983,
  .pop 982 1648 1649,
  .cx 1648 982,
  .pop 981 1647 1648,
  .cx 1647 981]
private def block680 : List Gate := [
  .pop 980 1646 1647,
  .cx 1646 980,
  .pop 979 1645 1646,
  .cx 1645 979,
  .pop 978 1644 1645,
  .cx 1644 978,
  .pop 977 1643 1644,
  .cx 1643 977,
  .pop 976 1642 1643,
  .cx 1642 976,
  .pop 975 1641 1642,
  .cx 1641 975,
  .pop 974 1640 1641,
  .cx 1640 974,
  .pop 973 1639 1640,
  .cx 1639 973,
  .pop 972 1638 1639,
  .cx 1638 972,
  .pop 971 1637 1638,
  .cx 1637 971,
  .pop 970 1636 1637,
  .cx 1636 970,
  .pop 969 1635 1636,
  .cx 1635 969,
  .pop 968 1634 1635,
  .cx 1634 968,
  .pop 967 1633 1634,
  .cx 1633 967,
  .pop 966 1632 1633,
  .cx 1632 966,
  .pop 965 1631 1632,
  .cx 1631 965,
  .pop 964 1630 1631,
  .cx 1630 964,
  .pop 963 1629 1630,
  .cx 1629 963,
  .pop 962 1628 1629,
  .cx 1628 962,
  .pop 961 1627 1628,
  .cx 1627 961]
private def block720 : List Gate := [
  .pop 960 1626 1627,
  .cx 1626 960,
  .pop 959 1625 1626,
  .cx 1625 959,
  .pop 958 1624 1625,
  .cx 1624 958]
private def block726 : List Gate := [
  .pop 957 1623 1624,
  .cx 1623 957,
  .pop 956 1622 1623,
  .cx 1622 956,
  .pop 955 1621 1622,
  .cx 1621 955,
  .pop 954 1620 1621,
  .cx 1620 954,
  .pop 953 1619 1620,
  .cx 1619 953,
  .pop 952 1618 1619,
  .cx 1618 952,
  .pop 951 1617 1618,
  .cx 1617 951,
  .pop 950 1616 1617,
  .cx 1616 950,
  .pop 949 1615 1616,
  .cx 1615 949,
  .pop 948 1614 1615,
  .cx 1614 948,
  .pop 947 1613 1614,
  .cx 1613 947,
  .pop 946 1612 1613,
  .cx 1612 946,
  .pop 945 1611 1612,
  .cx 1611 945,
  .pop 944 1610 1611,
  .cx 1610 944,
  .pop 943 1609 1610,
  .cx 1609 943,
  .pop 942 1608 1609,
  .cx 1608 942,
  .pop 941 1607 1608,
  .cx 1607 941]
private def block760 : List Gate := [
  .pop 940 1606 1607,
  .cx 1606 940,
  .pop 939 1605 1606,
  .cx 1605 939,
  .pop 938 1604 1605,
  .cx 1604 938,
  .pop 937 1603 1604,
  .cx 1603 937]
private def block768 : List Gate := [
  .pop 936 1602 1603,
  .cx 1602 936,
  .pop 935 1601 1602,
  .cx 1601 935,
  .pop 934 1600 1601,
  .cx 1600 934,
  .pop 1705 1599 1600,
  .cx 1599 1705,
  .pop 1704 1598 1599,
  .cx 1598 1704,
  .pop 1703 1709 1598,
  .cx 1709 1703,
  .cx 1597 1703,
  .cx 1597 1704,
  .cx 1597 1705,
  .cx 1597 934,
  .cx 1597 935,
  .cx 1597 936,
  .cx 1597 937,
  .cx 1597 938,
  .cx 1597 939,
  .cx 1597 940,
  .cx 1597 941,
  .cx 1597 942,
  .cx 1597 943,
  .cx 1597 944,
  .cx 1597 945,
  .cx 1597 946,
  .cx 1597 947,
  .cx 1597 948,
  .cx 1597 949,
  .cx 1597 950]
private def block800 : List Gate := [
  .cx 1597 951,
  .cx 1597 952,
  .cx 1597 953,
  .cx 1597 954,
  .cx 1597 955,
  .cx 1597 956,
  .cx 1597 957,
  .cx 1597 958,
  .cx 1597 959,
  .cx 1597 960,
  .cx 1597 961,
  .cx 1597 962,
  .cx 1597 963,
  .cx 1597 964,
  .cx 1597 965,
  .cx 1597 966,
  .cx 1597 967,
  .cx 1597 968,
  .cx 1597 969,
  .cx 1597 970,
  .cx 1597 971,
  .cx 1597 972]
private def block822 : List Gate := [
  .cx 1597 973,
  .cx 1597 974,
  .cx 1597 975,
  .cx 1597 976,
  .cx 1597 977,
  .cx 1597 978,
  .cx 1597 979,
  .cx 1597 980,
  .cx 1597 981,
  .cx 1597 982,
  .cx 1597 983,
  .cx 1597 984,
  .cx 1597 985,
  .cx 1597 986,
  .cx 1597 987,
  .cx 1597 988,
  .cx 1597 989,
  .cx 1597 990]
private def block840 : List Gate := [
  .cx 1597 991,
  .cx 1597 992,
  .cx 1597 993,
  .cx 1597 994,
  .cx 1597 995,
  .cx 1597 996,
  .cx 1597 997,
  .cx 1597 998,
  .cx 1597 999,
  .cx 1597 1000,
  .cx 1597 1001,
  .cx 1597 1002,
  .cx 1597 1003,
  .cx 1597 1004,
  .cx 1597 1005,
  .cx 1597 1006,
  .cx 1597 1007,
  .cx 1597 1008,
  .cx 1597 1009,
  .cx 1597 1010,
  .cx 1597 1011,
  .cx 1597 1012,
  .cx 1597 1013,
  .cx 1597 1014]
private def block864 : List Gate := [
  .cx 1597 1015,
  .cx 1597 1016,
  .cx 1597 1017,
  .cx 1597 1018,
  .cx 1597 1019,
  .cx 1597 1020,
  .cx 1597 1021,
  .cx 1597 1022,
  .cx 1597 1023,
  .cx 1597 1024,
  .cx 1597 1025,
  .cx 1597 1026,
  .cx 1597 1027,
  .cx 1597 1028,
  .cx 1597 1029,
  .cx 1597 1030]
private def block880 : List Gate := [
  .cx 1597 1031,
  .cx 1597 1032,
  .cx 1597 1033,
  .cx 1597 1034,
  .cx 1597 1035,
  .cx 1597 1036,
  .cx 1597 1037,
  .cx 1597 1038,
  .cx 1597 1039,
  .cx 1597 1040,
  .cx 1597 1041,
  .cx 1597 1042,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613,
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1042 1598,
  .ccx 1613 1598 1042,
  .cx 1042 1598,
  .cx 1041 1042,
  .ccx 1613 1042 1041,
  .cx 1041 1042,
  .cx 1040 1041,
  .ccx 1613 1041 1040,
  .cx 1040 1041,
  .cx 1039 1040,
  .ccx 1613 1040 1039,
  .cx 1039 1040,
  .cx 1038 1039,
  .ccx 1613 1039 1038,
  .cx 1038 1039,
  .cx 1037 1038,
  .ccx 1613 1038 1037,
  .cx 1037 1038]
private def block918 : List Gate := [
  .cx 1036 1037,
  .ccx 1613 1037 1036]
private def block920 : List Gate := [
  .cx 1036 1037,
  .cx 1035 1036,
  .ccx 1613 1036 1035,
  .cx 1035 1036,
  .cx 1034 1035,
  .ccx 1613 1035 1034,
  .cx 1034 1035,
  .cx 1033 1034,
  .ccx 1613 1034 1033,
  .cx 1033 1034,
  .cx 1032 1033,
  .ccx 1613 1033 1032,
  .cx 1032 1033,
  .cx 1031 1032,
  .ccx 1613 1032 1031,
  .cx 1031 1032,
  .cx 1030 1031,
  .ccx 1613 1031 1030,
  .cx 1030 1031,
  .cx 1029 1030,
  .ccx 1613 1030 1029,
  .cx 1029 1030,
  .cx 1028 1029,
  .ccx 1613 1029 1028,
  .cx 1028 1029,
  .cx 1027 1028,
  .ccx 1613 1028 1027,
  .cx 1027 1028,
  .cx 1026 1027,
  .ccx 1613 1027 1026,
  .cx 1026 1027,
  .cx 1025 1026,
  .ccx 1613 1026 1025,
  .cx 1025 1026,
  .cx 1024 1025,
  .ccx 1613 1025 1024,
  .cx 1024 1025,
  .cx 1023 1024,
  .ccx 1613 1024 1023,
  .cx 1023 1024]
private def block960 : List Gate := [
  .cx 1022 1023,
  .ccx 1613 1023 1022,
  .cx 1022 1023,
  .cx 1021 1022,
  .ccx 1613 1022 1021,
  .cx 1021 1022,
  .cx 1020 1021,
  .ccx 1613 1021 1020,
  .cx 1020 1021,
  .cx 1019 1020,
  .ccx 1613 1020 1019,
  .cx 1019 1020,
  .cx 1018 1019,
  .ccx 1613 1019 1018,
  .cx 1018 1019,
  .cx 1017 1018,
  .ccx 1613 1018 1017,
  .cx 1017 1018,
  .cx 1016 1017,
  .ccx 1613 1017 1016,
  .cx 1016 1017,
  .cx 1015 1016,
  .ccx 1613 1016 1015,
  .cx 1015 1016,
  .cx 1014 1015,
  .ccx 1613 1015 1014,
  .cx 1014 1015,
  .cx 1013 1014,
  .ccx 1613 1014 1013,
  .cx 1013 1014,
  .cx 1012 1013,
  .ccx 1613 1013 1012,
  .cx 1012 1013,
  .cx 1011 1012,
  .ccx 1613 1012 1011,
  .cx 1011 1012,
  .cx 1010 1011,
  .ccx 1613 1011 1010,
  .cx 1010 1011,
  .cx 1009 1010]
private def block1000 : List Gate := [
  .ccx 1613 1010 1009,
  .cx 1009 1010,
  .cx 1008 1009,
  .ccx 1613 1009 1008,
  .cx 1008 1009,
  .cx 1007 1008,
  .ccx 1613 1008 1007,
  .cx 1007 1008,
  .cx 1006 1007,
  .ccx 1613 1007 1006,
  .cx 1006 1007,
  .cx 1005 1006,
  .ccx 1613 1006 1005,
  .cx 1005 1006]
private def block1014 : List Gate := [
  .cx 1004 1005,
  .ccx 1613 1005 1004,
  .cx 1004 1005,
  .cx 1003 1004,
  .ccx 1613 1004 1003,
  .cx 1003 1004,
  .cx 1002 1003,
  .ccx 1613 1003 1002,
  .cx 1002 1003,
  .cx 1001 1002,
  .ccx 1613 1002 1001,
  .cx 1001 1002,
  .cx 1000 1001,
  .ccx 1613 1001 1000,
  .cx 1000 1001,
  .cx 999 1000,
  .ccx 1613 1000 999,
  .cx 999 1000,
  .cx 998 999,
  .ccx 1613 999 998,
  .cx 998 999,
  .cx 997 998,
  .ccx 1613 998 997,
  .cx 997 998,
  .cx 996 997,
  .ccx 1613 997 996]
private def block1040 : List Gate := [
  .cx 996 997,
  .cx 995 996,
  .ccx 1613 996 995,
  .cx 995 996,
  .cx 994 995,
  .ccx 1613 995 994,
  .cx 994 995,
  .cx 993 994,
  .ccx 1613 994 993,
  .cx 993 994,
  .cx 992 993,
  .ccx 1613 993 992,
  .cx 992 993,
  .cx 991 992,
  .ccx 1613 992 991,
  .cx 991 992]
private def block1056 : List Gate := [
  .cx 990 991,
  .ccx 1613 991 990,
  .cx 990 991,
  .cx 989 990,
  .ccx 1613 990 989,
  .cx 989 990,
  .cx 988 989,
  .ccx 1613 989 988,
  .cx 988 989,
  .cx 987 988,
  .ccx 1613 988 987,
  .cx 987 988,
  .cx 986 987,
  .ccx 1613 987 986,
  .cx 986 987,
  .cx 985 986,
  .ccx 1613 986 985,
  .cx 985 986,
  .cx 984 985,
  .ccx 1613 985 984,
  .cx 984 985,
  .cx 983 984,
  .ccx 1613 984 983,
  .cx 983 984]
private def block1080 : List Gate := [
  .cx 982 983,
  .ccx 1613 983 982,
  .cx 982 983,
  .cx 981 982,
  .ccx 1613 982 981,
  .cx 981 982,
  .cx 980 981,
  .ccx 1613 981 980,
  .cx 980 981,
  .cx 979 980,
  .ccx 1613 980 979,
  .cx 979 980,
  .cx 978 979,
  .ccx 1613 979 978,
  .cx 978 979,
  .cx 977 978,
  .ccx 1613 978 977,
  .cx 977 978,
  .cx 976 977,
  .ccx 1613 977 976,
  .cx 976 977,
  .cx 975 976,
  .ccx 1613 976 975,
  .cx 975 976,
  .cx 974 975,
  .ccx 1613 975 974,
  .cx 974 975,
  .cx 973 974,
  .ccx 1613 974 973,
  .cx 973 974]
private def block1110 : List Gate := [
  .cx 972 973,
  .ccx 1613 973 972,
  .cx 972 973,
  .cx 971 972,
  .ccx 1613 972 971,
  .cx 971 972,
  .cx 970 971,
  .ccx 1613 971 970,
  .cx 970 971,
  .cx 969 970]
private def block1120 : List Gate := [
  .ccx 1613 970 969,
  .cx 969 970,
  .cx 968 969,
  .ccx 1613 969 968,
  .cx 968 969,
  .cx 967 968,
  .ccx 1613 968 967,
  .cx 967 968,
  .cx 966 967,
  .ccx 1613 967 966,
  .cx 966 967,
  .cx 965 966,
  .ccx 1613 966 965,
  .cx 965 966,
  .cx 964 965,
  .ccx 1613 965 964,
  .cx 964 965,
  .cx 963 964,
  .ccx 1613 964 963,
  .cx 963 964,
  .cx 962 963,
  .ccx 1613 963 962,
  .cx 962 963,
  .cx 961 962,
  .ccx 1613 962 961,
  .cx 961 962,
  .cx 960 961,
  .ccx 1613 961 960,
  .cx 960 961,
  .cx 959 960,
  .ccx 1613 960 959,
  .cx 959 960]
private def block1152 : List Gate := [
  .cx 958 959,
  .ccx 1613 959 958,
  .cx 958 959,
  .cx 957 958,
  .ccx 1613 958 957,
  .cx 957 958,
  .cx 956 957,
  .ccx 1613 957 956]
private def block1160 : List Gate := [
  .cx 956 957,
  .cx 955 956,
  .ccx 1613 956 955,
  .cx 955 956,
  .cx 954 955,
  .ccx 1613 955 954,
  .cx 954 955,
  .cx 953 954,
  .ccx 1613 954 953,
  .cx 953 954,
  .cx 952 953,
  .ccx 1613 953 952,
  .cx 952 953,
  .cx 951 952,
  .ccx 1613 952 951,
  .cx 951 952,
  .cx 950 951,
  .ccx 1613 951 950,
  .cx 950 951,
  .cx 949 950,
  .ccx 1613 950 949,
  .cx 949 950,
  .cx 948 949,
  .ccx 1613 949 948,
  .cx 948 949,
  .cx 947 948,
  .ccx 1613 948 947,
  .cx 947 948,
  .cx 946 947,
  .ccx 1613 947 946,
  .cx 946 947,
  .cx 945 946,
  .ccx 1613 946 945,
  .cx 945 946,
  .cx 944 945,
  .ccx 1613 945 944,
  .cx 944 945,
  .cx 943 944,
  .ccx 1613 944 943,
  .cx 943 944]
private def block1200 : List Gate := [
  .cx 942 943,
  .ccx 1613 943 942,
  .cx 942 943,
  .cx 941 942,
  .ccx 1613 942 941,
  .cx 941 942]
private def block1206 : List Gate := [
  .cx 940 941,
  .ccx 1613 941 940,
  .cx 940 941,
  .cx 939 940,
  .ccx 1613 940 939,
  .cx 939 940,
  .cx 938 939,
  .ccx 1613 939 938,
  .cx 938 939,
  .cx 937 938,
  .ccx 1613 938 937,
  .cx 937 938,
  .cx 936 937,
  .ccx 1613 937 936,
  .cx 936 937,
  .cx 935 936,
  .ccx 1613 936 935,
  .cx 935 936,
  .cx 934 935,
  .ccx 1613 935 934,
  .cx 934 935,
  .cx 1705 934,
  .ccx 1613 934 1705,
  .cx 1705 934,
  .cx 1704 1705,
  .ccx 1613 1705 1704,
  .cx 1704 1705,
  .cx 1703 1704,
  .ccx 1613 1704 1703,
  .cx 1703 1704,
  .cx 1562 1613,
  .cx 1564 1613,
  .cx 1566 1613,
  .cx 1568 1613]
private def block1240 : List Gate := [
  .cx 1570 1613,
  .cx 1572 1613,
  .cx 1574 1613,
  .cx 1560 1613,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613]
private def block1248 : List Gate := [
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1598 1600,
  .ccx 1613 1600 1598,
  .cx 1598 1600,
  .cx 1042 1599,
  .ccx 1613 1599 1042,
  .cx 1042 1599,
  .cx 1041 1598,
  .ccx 1613 1598 1041,
  .cx 1041 1598,
  .cx 1040 1042,
  .ccx 1613 1042 1040,
  .cx 1040 1042,
  .cx 1039 1041,
  .ccx 1613 1041 1039,
  .cx 1039 1041,
  .cx 1038 1040,
  .ccx 1613 1040 1038,
  .cx 1038 1040,
  .cx 1037 1039,
  .ccx 1613 1039 1037,
  .cx 1037 1039,
  .cx 1036 1038,
  .ccx 1613 1038 1036,
  .cx 1036 1038,
  .cx 1035 1037,
  .ccx 1613 1037 1035,
  .cx 1035 1037,
  .cx 1034 1036]
private def block1280 : List Gate := [
  .ccx 1613 1036 1034,
  .cx 1034 1036,
  .cx 1033 1035,
  .ccx 1613 1035 1033,
  .cx 1033 1035,
  .cx 1032 1034,
  .ccx 1613 1034 1032,
  .cx 1032 1034,
  .cx 1031 1033,
  .ccx 1613 1033 1031,
  .cx 1031 1033,
  .cx 1030 1032,
  .ccx 1613 1032 1030,
  .cx 1030 1032,
  .cx 1029 1031,
  .ccx 1613 1031 1029,
  .cx 1029 1031,
  .cx 1028 1030,
  .ccx 1613 1030 1028,
  .cx 1028 1030,
  .cx 1027 1029,
  .ccx 1613 1029 1027]
private def block1302 : List Gate := [
  .cx 1027 1029,
  .cx 1026 1028,
  .ccx 1613 1028 1026,
  .cx 1026 1028,
  .cx 1025 1027,
  .ccx 1613 1027 1025,
  .cx 1025 1027,
  .cx 1024 1026,
  .ccx 1613 1026 1024,
  .cx 1024 1026,
  .cx 1023 1025,
  .ccx 1613 1025 1023,
  .cx 1023 1025,
  .cx 1022 1024,
  .ccx 1613 1024 1022,
  .cx 1022 1024,
  .cx 1021 1023,
  .ccx 1613 1023 1021]
private def block1320 : List Gate := [
  .cx 1021 1023,
  .cx 1020 1022,
  .ccx 1613 1022 1020,
  .cx 1020 1022,
  .cx 1019 1021,
  .ccx 1613 1021 1019,
  .cx 1019 1021,
  .cx 1018 1020,
  .ccx 1613 1020 1018,
  .cx 1018 1020,
  .cx 1017 1019,
  .ccx 1613 1019 1017,
  .cx 1017 1019,
  .cx 1016 1018,
  .ccx 1613 1018 1016,
  .cx 1016 1018,
  .cx 1015 1017,
  .ccx 1613 1017 1015,
  .cx 1015 1017,
  .cx 1014 1016,
  .ccx 1613 1016 1014,
  .cx 1014 1016,
  .cx 1013 1015,
  .ccx 1613 1015 1013]
private def block1344 : List Gate := [
  .cx 1013 1015,
  .cx 1012 1014,
  .ccx 1613 1014 1012,
  .cx 1012 1014,
  .cx 1011 1013,
  .ccx 1613 1013 1011,
  .cx 1011 1013,
  .cx 1010 1012,
  .ccx 1613 1012 1010,
  .cx 1010 1012,
  .cx 1009 1011,
  .ccx 1613 1011 1009,
  .cx 1009 1011,
  .cx 1008 1010,
  .ccx 1613 1010 1008,
  .cx 1008 1010]
private def block1360 : List Gate := [
  .cx 1007 1009,
  .ccx 1613 1009 1007,
  .cx 1007 1009,
  .cx 1006 1008,
  .ccx 1613 1008 1006,
  .cx 1006 1008,
  .cx 1005 1007,
  .ccx 1613 1007 1005,
  .cx 1005 1007,
  .cx 1004 1006,
  .ccx 1613 1006 1004,
  .cx 1004 1006,
  .cx 1003 1005,
  .ccx 1613 1005 1003,
  .cx 1003 1005,
  .cx 1002 1004,
  .ccx 1613 1004 1002,
  .cx 1002 1004,
  .cx 1001 1003,
  .ccx 1613 1003 1001,
  .cx 1001 1003,
  .cx 1000 1002,
  .ccx 1613 1002 1000,
  .cx 1000 1002,
  .cx 999 1001,
  .ccx 1613 1001 999,
  .cx 999 1001,
  .cx 998 1000,
  .ccx 1613 1000 998,
  .cx 998 1000,
  .cx 997 999,
  .ccx 1613 999 997,
  .cx 997 999,
  .cx 996 998,
  .ccx 1613 998 996,
  .cx 996 998,
  .cx 995 997,
  .ccx 1613 997 995]
private def block1398 : List Gate := [
  .cx 995 997,
  .cx 994 996]
private def block1400 : List Gate := [
  .ccx 1613 996 994,
  .cx 994 996,
  .cx 993 995,
  .ccx 1613 995 993,
  .cx 993 995,
  .cx 992 994,
  .ccx 1613 994 992,
  .cx 992 994,
  .cx 991 993,
  .ccx 1613 993 991,
  .cx 991 993,
  .cx 990 992,
  .ccx 1613 992 990,
  .cx 990 992,
  .cx 989 991,
  .ccx 1613 991 989,
  .cx 989 991,
  .cx 988 990,
  .ccx 1613 990 988,
  .cx 988 990,
  .cx 987 989,
  .ccx 1613 989 987,
  .cx 987 989,
  .cx 986 988,
  .ccx 1613 988 986,
  .cx 986 988,
  .cx 985 987,
  .ccx 1613 987 985,
  .cx 985 987,
  .cx 984 986,
  .ccx 1613 986 984,
  .cx 984 986,
  .cx 983 985,
  .ccx 1613 985 983,
  .cx 983 985,
  .cx 982 984,
  .ccx 1613 984 982,
  .cx 982 984,
  .cx 981 983,
  .ccx 1613 983 981]
private def block1440 : List Gate := [
  .cx 981 983,
  .cx 980 982,
  .ccx 1613 982 980,
  .cx 980 982,
  .cx 979 981,
  .ccx 1613 981 979,
  .cx 979 981,
  .cx 978 980,
  .ccx 1613 980 978,
  .cx 978 980,
  .cx 977 979,
  .ccx 1613 979 977,
  .cx 977 979,
  .cx 976 978,
  .ccx 1613 978 976,
  .cx 976 978,
  .cx 975 977,
  .ccx 1613 977 975,
  .cx 975 977,
  .cx 974 976,
  .ccx 1613 976 974,
  .cx 974 976,
  .cx 973 975,
  .ccx 1613 975 973,
  .cx 973 975,
  .cx 972 974,
  .ccx 1613 974 972,
  .cx 972 974,
  .cx 971 973,
  .ccx 1613 973 971,
  .cx 971 973,
  .cx 970 972,
  .ccx 1613 972 970,
  .cx 970 972,
  .cx 969 971,
  .ccx 1613 971 969,
  .cx 969 971,
  .cx 968 970,
  .ccx 1613 970 968,
  .cx 968 970]
private def block1480 : List Gate := [
  .cx 967 969,
  .ccx 1613 969 967,
  .cx 967 969,
  .cx 966 968,
  .ccx 1613 968 966,
  .cx 966 968,
  .cx 965 967,
  .ccx 1613 967 965,
  .cx 965 967,
  .cx 964 966,
  .ccx 1613 966 964,
  .cx 964 966,
  .cx 963 965,
  .ccx 1613 965 963]
private def block1494 : List Gate := [
  .cx 963 965,
  .cx 962 964,
  .ccx 1613 964 962,
  .cx 962 964,
  .cx 961 963,
  .ccx 1613 963 961,
  .cx 961 963,
  .cx 960 962,
  .ccx 1613 962 960,
  .cx 960 962,
  .cx 959 961,
  .ccx 1613 961 959,
  .cx 959 961,
  .cx 958 960,
  .ccx 1613 960 958,
  .cx 958 960,
  .cx 957 959,
  .ccx 1613 959 957,
  .cx 957 959,
  .cx 956 958,
  .ccx 1613 958 956,
  .cx 956 958,
  .cx 955 957,
  .ccx 1613 957 955,
  .cx 955 957,
  .cx 954 956]
private def block1520 : List Gate := [
  .ccx 1613 956 954,
  .cx 954 956,
  .cx 953 955,
  .ccx 1613 955 953,
  .cx 953 955,
  .cx 952 954,
  .ccx 1613 954 952,
  .cx 952 954,
  .cx 951 953,
  .ccx 1613 953 951,
  .cx 951 953,
  .cx 950 952,
  .ccx 1613 952 950,
  .cx 950 952,
  .cx 949 951,
  .ccx 1613 951 949]
private def block1536 : List Gate := [
  .cx 949 951,
  .cx 948 950,
  .ccx 1613 950 948,
  .cx 948 950,
  .cx 947 949,
  .ccx 1613 949 947,
  .cx 947 949,
  .cx 946 948,
  .ccx 1613 948 946,
  .cx 946 948,
  .cx 945 947,
  .ccx 1613 947 945,
  .cx 945 947,
  .cx 944 946,
  .ccx 1613 946 944,
  .cx 944 946,
  .cx 943 945,
  .ccx 1613 945 943,
  .cx 943 945,
  .cx 942 944,
  .ccx 1613 944 942,
  .cx 942 944,
  .cx 941 943,
  .ccx 1613 943 941]
private def block1560 : List Gate := [
  .cx 941 943,
  .cx 940 942,
  .ccx 1613 942 940,
  .cx 940 942,
  .cx 939 941,
  .ccx 1613 941 939,
  .cx 939 941,
  .cx 938 940,
  .ccx 1613 940 938,
  .cx 938 940,
  .cx 937 939,
  .ccx 1613 939 937,
  .cx 937 939,
  .cx 936 938,
  .ccx 1613 938 936,
  .cx 936 938,
  .cx 935 937,
  .ccx 1613 937 935,
  .cx 935 937,
  .cx 934 936,
  .ccx 1613 936 934,
  .cx 934 936,
  .cx 1705 935,
  .ccx 1613 935 1705,
  .cx 1705 935,
  .cx 1704 934,
  .ccx 1613 934 1704,
  .cx 1704 934,
  .cx 1703 1705,
  .ccx 1613 1705 1703]
private def block1590 : List Gate := [
  .cx 1703 1705,
  .cx 1563 1613,
  .cx 1564 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1565 1613]
private def block1600 : List Gate := [
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1600 1604,
  .ccx 1613 1604 1600,
  .cx 1600 1604,
  .cx 1599 1603,
  .ccx 1613 1603 1599,
  .cx 1599 1603,
  .cx 1598 1602,
  .ccx 1613 1602 1598,
  .cx 1598 1602,
  .cx 1042 1601,
  .ccx 1613 1601 1042,
  .cx 1042 1601,
  .cx 1041 1600,
  .ccx 1613 1600 1041,
  .cx 1041 1600,
  .cx 1040 1599,
  .ccx 1613 1599 1040,
  .cx 1040 1599,
  .cx 1039 1598,
  .ccx 1613 1598 1039,
  .cx 1039 1598,
  .cx 1038 1042,
  .ccx 1613 1042 1038,
  .cx 1038 1042,
  .cx 1037 1041]
private def block1632 : List Gate := [
  .ccx 1613 1041 1037,
  .cx 1037 1041,
  .cx 1036 1040,
  .ccx 1613 1040 1036,
  .cx 1036 1040,
  .cx 1035 1039,
  .ccx 1613 1039 1035,
  .cx 1035 1039]
private def block1640 : List Gate := [
  .cx 1034 1038,
  .ccx 1613 1038 1034,
  .cx 1034 1038,
  .cx 1033 1037,
  .ccx 1613 1037 1033,
  .cx 1033 1037,
  .cx 1032 1036,
  .ccx 1613 1036 1032,
  .cx 1032 1036,
  .cx 1031 1035,
  .ccx 1613 1035 1031,
  .cx 1031 1035,
  .cx 1030 1034,
  .ccx 1613 1034 1030,
  .cx 1030 1034,
  .cx 1029 1033,
  .ccx 1613 1033 1029,
  .cx 1029 1033,
  .cx 1028 1032,
  .ccx 1613 1032 1028,
  .cx 1028 1032,
  .cx 1027 1031,
  .ccx 1613 1031 1027,
  .cx 1027 1031,
  .cx 1026 1030,
  .ccx 1613 1030 1026,
  .cx 1026 1030,
  .cx 1025 1029,
  .ccx 1613 1029 1025,
  .cx 1025 1029,
  .cx 1024 1028,
  .ccx 1613 1028 1024,
  .cx 1024 1028,
  .cx 1023 1027,
  .ccx 1613 1027 1023,
  .cx 1023 1027,
  .cx 1022 1026,
  .ccx 1613 1026 1022,
  .cx 1022 1026,
  .cx 1021 1025]
private def block1680 : List Gate := [
  .ccx 1613 1025 1021,
  .cx 1021 1025,
  .cx 1020 1024,
  .ccx 1613 1024 1020,
  .cx 1020 1024,
  .cx 1019 1023]
private def block1686 : List Gate := [
  .ccx 1613 1023 1019,
  .cx 1019 1023,
  .cx 1018 1022,
  .ccx 1613 1022 1018,
  .cx 1018 1022,
  .cx 1017 1021,
  .ccx 1613 1021 1017,
  .cx 1017 1021,
  .cx 1016 1020,
  .ccx 1613 1020 1016,
  .cx 1016 1020,
  .cx 1015 1019,
  .ccx 1613 1019 1015,
  .cx 1015 1019,
  .cx 1014 1018,
  .ccx 1613 1018 1014,
  .cx 1014 1018,
  .cx 1013 1017,
  .ccx 1613 1017 1013,
  .cx 1013 1017,
  .cx 1012 1016,
  .ccx 1613 1016 1012,
  .cx 1012 1016,
  .cx 1011 1015,
  .ccx 1613 1015 1011,
  .cx 1011 1015,
  .cx 1010 1014,
  .ccx 1613 1014 1010,
  .cx 1010 1014,
  .cx 1009 1013,
  .ccx 1613 1013 1009,
  .cx 1009 1013,
  .cx 1008 1012,
  .ccx 1613 1012 1008]
private def block1720 : List Gate := [
  .cx 1008 1012,
  .cx 1007 1011,
  .ccx 1613 1011 1007,
  .cx 1007 1011,
  .cx 1006 1010,
  .ccx 1613 1010 1006,
  .cx 1006 1010,
  .cx 1005 1009]
private def block1728 : List Gate := [
  .ccx 1613 1009 1005,
  .cx 1005 1009,
  .cx 1004 1008,
  .ccx 1613 1008 1004,
  .cx 1004 1008,
  .cx 1003 1007,
  .ccx 1613 1007 1003,
  .cx 1003 1007,
  .cx 1002 1006,
  .ccx 1613 1006 1002,
  .cx 1002 1006,
  .cx 1001 1005,
  .ccx 1613 1005 1001,
  .cx 1001 1005,
  .cx 1000 1004,
  .ccx 1613 1004 1000,
  .cx 1000 1004,
  .cx 999 1003,
  .ccx 1613 1003 999,
  .cx 999 1003,
  .cx 998 1002,
  .ccx 1613 1002 998,
  .cx 998 1002,
  .cx 997 1001,
  .ccx 1613 1001 997,
  .cx 997 1001,
  .cx 996 1000,
  .ccx 1613 1000 996,
  .cx 996 1000,
  .cx 995 999,
  .ccx 1613 999 995,
  .cx 995 999]
private def block1760 : List Gate := [
  .cx 994 998,
  .ccx 1613 998 994,
  .cx 994 998,
  .cx 993 997,
  .ccx 1613 997 993,
  .cx 993 997,
  .cx 992 996,
  .ccx 1613 996 992,
  .cx 992 996,
  .cx 991 995,
  .ccx 1613 995 991,
  .cx 991 995,
  .cx 990 994,
  .ccx 1613 994 990,
  .cx 990 994,
  .cx 989 993,
  .ccx 1613 993 989,
  .cx 989 993,
  .cx 988 992,
  .ccx 1613 992 988,
  .cx 988 992,
  .cx 987 991]
private def block1782 : List Gate := [
  .ccx 1613 991 987,
  .cx 987 991,
  .cx 986 990,
  .ccx 1613 990 986,
  .cx 986 990,
  .cx 985 989,
  .ccx 1613 989 985,
  .cx 985 989,
  .cx 984 988,
  .ccx 1613 988 984,
  .cx 984 988,
  .cx 983 987,
  .ccx 1613 987 983,
  .cx 983 987,
  .cx 982 986,
  .ccx 1613 986 982,
  .cx 982 986,
  .cx 981 985]
private def block1800 : List Gate := [
  .ccx 1613 985 981,
  .cx 981 985,
  .cx 980 984,
  .ccx 1613 984 980,
  .cx 980 984,
  .cx 979 983,
  .ccx 1613 983 979,
  .cx 979 983,
  .cx 978 982,
  .ccx 1613 982 978,
  .cx 978 982,
  .cx 977 981,
  .ccx 1613 981 977,
  .cx 977 981,
  .cx 976 980,
  .ccx 1613 980 976,
  .cx 976 980,
  .cx 975 979,
  .ccx 1613 979 975,
  .cx 975 979,
  .cx 974 978,
  .ccx 1613 978 974,
  .cx 974 978,
  .cx 973 977]
private def block1824 : List Gate := [
  .ccx 1613 977 973,
  .cx 973 977,
  .cx 972 976,
  .ccx 1613 976 972,
  .cx 972 976,
  .cx 971 975,
  .ccx 1613 975 971,
  .cx 971 975,
  .cx 970 974,
  .ccx 1613 974 970,
  .cx 970 974,
  .cx 969 973,
  .ccx 1613 973 969,
  .cx 969 973,
  .cx 968 972,
  .ccx 1613 972 968]
private def block1840 : List Gate := [
  .cx 968 972,
  .cx 967 971,
  .ccx 1613 971 967,
  .cx 967 971,
  .cx 966 970,
  .ccx 1613 970 966,
  .cx 966 970,
  .cx 965 969,
  .ccx 1613 969 965,
  .cx 965 969,
  .cx 964 968,
  .ccx 1613 968 964,
  .cx 964 968,
  .cx 963 967,
  .ccx 1613 967 963,
  .cx 963 967,
  .cx 962 966,
  .ccx 1613 966 962,
  .cx 962 966,
  .cx 961 965,
  .ccx 1613 965 961,
  .cx 961 965,
  .cx 960 964,
  .ccx 1613 964 960,
  .cx 960 964,
  .cx 959 963,
  .ccx 1613 963 959,
  .cx 959 963,
  .cx 958 962,
  .ccx 1613 962 958,
  .cx 958 962,
  .cx 957 961,
  .ccx 1613 961 957,
  .cx 957 961,
  .cx 956 960,
  .ccx 1613 960 956,
  .cx 956 960,
  .cx 955 959]
private def block1878 : List Gate := [
  .ccx 1613 959 955,
  .cx 955 959]
private def block1880 : List Gate := [
  .cx 954 958,
  .ccx 1613 958 954,
  .cx 954 958,
  .cx 953 957,
  .ccx 1613 957 953,
  .cx 953 957,
  .cx 952 956,
  .ccx 1613 956 952,
  .cx 952 956,
  .cx 951 955,
  .ccx 1613 955 951,
  .cx 951 955,
  .cx 950 954,
  .ccx 1613 954 950,
  .cx 950 954,
  .cx 949 953,
  .ccx 1613 953 949,
  .cx 949 953,
  .cx 948 952,
  .ccx 1613 952 948,
  .cx 948 952,
  .cx 947 951,
  .ccx 1613 951 947,
  .cx 947 951,
  .cx 946 950,
  .ccx 1613 950 946,
  .cx 946 950,
  .cx 945 949,
  .ccx 1613 949 945,
  .cx 945 949,
  .cx 944 948,
  .ccx 1613 948 944,
  .cx 944 948,
  .cx 943 947,
  .ccx 1613 947 943,
  .cx 943 947,
  .cx 942 946,
  .ccx 1613 946 942,
  .cx 942 946,
  .cx 941 945]
private def block1920 : List Gate := [
  .ccx 1613 945 941,
  .cx 941 945,
  .cx 940 944,
  .ccx 1613 944 940,
  .cx 940 944,
  .cx 939 943,
  .ccx 1613 943 939,
  .cx 939 943,
  .cx 938 942,
  .ccx 1613 942 938,
  .cx 938 942,
  .cx 937 941,
  .ccx 1613 941 937,
  .cx 937 941,
  .cx 936 940,
  .ccx 1613 940 936,
  .cx 936 940,
  .cx 935 939,
  .ccx 1613 939 935,
  .cx 935 939,
  .cx 934 938,
  .ccx 1613 938 934,
  .cx 934 938,
  .cx 1705 937,
  .ccx 1613 937 1705,
  .cx 1705 937,
  .cx 1704 936,
  .ccx 1613 936 1704,
  .cx 1704 936,
  .cx 1703 935,
  .ccx 1613 935 1703,
  .cx 1703 935,
  .cx 1565 1613,
  .cx 1566 1613,
  .cx 1567 1613,
  .cx 1568 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613]
private def block1960 : List Gate := [
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .cx 1604 1612,
  .ccx 1613 1612 1604,
  .cx 1604 1612,
  .cx 1603 1611,
  .ccx 1613 1611 1603,
  .cx 1603 1611]
private def block1974 : List Gate := [
  .cx 1602 1610,
  .ccx 1613 1610 1602,
  .cx 1602 1610,
  .cx 1601 1609,
  .ccx 1613 1609 1601,
  .cx 1601 1609,
  .cx 1600 1608,
  .ccx 1613 1608 1600,
  .cx 1600 1608,
  .cx 1599 1607,
  .ccx 1613 1607 1599,
  .cx 1599 1607,
  .cx 1598 1606,
  .ccx 1613 1606 1598,
  .cx 1598 1606,
  .cx 1042 1605,
  .ccx 1613 1605 1042,
  .cx 1042 1605,
  .cx 1041 1604,
  .ccx 1613 1604 1041,
  .cx 1041 1604,
  .cx 1040 1603,
  .ccx 1613 1603 1040,
  .cx 1040 1603,
  .cx 1039 1602,
  .ccx 1613 1602 1039]
private def block2000 : List Gate := [
  .cx 1039 1602,
  .cx 1038 1601,
  .ccx 1613 1601 1038,
  .cx 1038 1601,
  .cx 1037 1600,
  .ccx 1613 1600 1037,
  .cx 1037 1600,
  .cx 1036 1599,
  .ccx 1613 1599 1036,
  .cx 1036 1599,
  .cx 1035 1598,
  .ccx 1613 1598 1035,
  .cx 1035 1598,
  .cx 1034 1042,
  .ccx 1613 1042 1034,
  .cx 1034 1042]
private def block2016 : List Gate := [
  .cx 1033 1041,
  .ccx 1613 1041 1033,
  .cx 1033 1041,
  .cx 1032 1040,
  .ccx 1613 1040 1032,
  .cx 1032 1040,
  .cx 1031 1039,
  .ccx 1613 1039 1031,
  .cx 1031 1039,
  .cx 1030 1038,
  .ccx 1613 1038 1030,
  .cx 1030 1038,
  .cx 1029 1037,
  .ccx 1613 1037 1029,
  .cx 1029 1037,
  .cx 1028 1036,
  .ccx 1613 1036 1028,
  .cx 1028 1036,
  .cx 1027 1035,
  .ccx 1613 1035 1027,
  .cx 1027 1035,
  .cx 1026 1034,
  .ccx 1613 1034 1026,
  .cx 1026 1034]
private def block2040 : List Gate := [
  .cx 1025 1033,
  .ccx 1613 1033 1025,
  .cx 1025 1033,
  .cx 1024 1032,
  .ccx 1613 1032 1024,
  .cx 1024 1032,
  .cx 1023 1031,
  .ccx 1613 1031 1023,
  .cx 1023 1031,
  .cx 1022 1030,
  .ccx 1613 1030 1022,
  .cx 1022 1030,
  .cx 1021 1029,
  .ccx 1613 1029 1021,
  .cx 1021 1029,
  .cx 1020 1028,
  .ccx 1613 1028 1020,
  .cx 1020 1028,
  .cx 1019 1027,
  .ccx 1613 1027 1019,
  .cx 1019 1027,
  .cx 1018 1026,
  .ccx 1613 1026 1018,
  .cx 1018 1026,
  .cx 1017 1025,
  .ccx 1613 1025 1017,
  .cx 1017 1025,
  .cx 1016 1024,
  .ccx 1613 1024 1016,
  .cx 1016 1024]
private def block2070 : List Gate := [
  .cx 1015 1023,
  .ccx 1613 1023 1015,
  .cx 1015 1023,
  .cx 1014 1022,
  .ccx 1613 1022 1014,
  .cx 1014 1022,
  .cx 1013 1021,
  .ccx 1613 1021 1013,
  .cx 1013 1021,
  .cx 1012 1020]
private def block2080 : List Gate := [
  .ccx 1613 1020 1012,
  .cx 1012 1020,
  .cx 1011 1019,
  .ccx 1613 1019 1011,
  .cx 1011 1019,
  .cx 1010 1018,
  .ccx 1613 1018 1010,
  .cx 1010 1018,
  .cx 1009 1017,
  .ccx 1613 1017 1009,
  .cx 1009 1017,
  .cx 1008 1016,
  .ccx 1613 1016 1008,
  .cx 1008 1016,
  .cx 1007 1015,
  .ccx 1613 1015 1007,
  .cx 1007 1015,
  .cx 1006 1014,
  .ccx 1613 1014 1006,
  .cx 1006 1014,
  .cx 1005 1013,
  .ccx 1613 1013 1005,
  .cx 1005 1013,
  .cx 1004 1012,
  .ccx 1613 1012 1004,
  .cx 1004 1012,
  .cx 1003 1011,
  .ccx 1613 1011 1003,
  .cx 1003 1011,
  .cx 1002 1010,
  .ccx 1613 1010 1002,
  .cx 1002 1010]
private def block2112 : List Gate := [
  .cx 1001 1009,
  .ccx 1613 1009 1001,
  .cx 1001 1009,
  .cx 1000 1008,
  .ccx 1613 1008 1000,
  .cx 1000 1008,
  .cx 999 1007,
  .ccx 1613 1007 999]
private def block2120 : List Gate := [
  .cx 999 1007,
  .cx 998 1006,
  .ccx 1613 1006 998,
  .cx 998 1006,
  .cx 997 1005,
  .ccx 1613 1005 997,
  .cx 997 1005,
  .cx 996 1004,
  .ccx 1613 1004 996,
  .cx 996 1004,
  .cx 995 1003,
  .ccx 1613 1003 995,
  .cx 995 1003,
  .cx 994 1002,
  .ccx 1613 1002 994,
  .cx 994 1002,
  .cx 993 1001,
  .ccx 1613 1001 993,
  .cx 993 1001,
  .cx 992 1000,
  .ccx 1613 1000 992,
  .cx 992 1000,
  .cx 991 999,
  .ccx 1613 999 991,
  .cx 991 999,
  .cx 990 998,
  .ccx 1613 998 990,
  .cx 990 998,
  .cx 989 997,
  .ccx 1613 997 989,
  .cx 989 997,
  .cx 988 996,
  .ccx 1613 996 988,
  .cx 988 996,
  .cx 987 995,
  .ccx 1613 995 987,
  .cx 987 995,
  .cx 986 994,
  .ccx 1613 994 986,
  .cx 986 994]
private def block2160 : List Gate := [
  .cx 985 993,
  .ccx 1613 993 985,
  .cx 985 993,
  .cx 984 992,
  .ccx 1613 992 984,
  .cx 984 992]
private def block2166 : List Gate := [
  .cx 983 991,
  .ccx 1613 991 983,
  .cx 983 991,
  .cx 982 990,
  .ccx 1613 990 982,
  .cx 982 990,
  .cx 981 989,
  .ccx 1613 989 981,
  .cx 981 989,
  .cx 980 988,
  .ccx 1613 988 980,
  .cx 980 988,
  .cx 979 987,
  .ccx 1613 987 979,
  .cx 979 987,
  .cx 978 986,
  .ccx 1613 986 978,
  .cx 978 986,
  .cx 977 985,
  .ccx 1613 985 977,
  .cx 977 985,
  .cx 976 984,
  .ccx 1613 984 976,
  .cx 976 984,
  .cx 975 983,
  .ccx 1613 983 975,
  .cx 975 983,
  .cx 974 982,
  .ccx 1613 982 974,
  .cx 974 982,
  .cx 973 981,
  .ccx 1613 981 973,
  .cx 973 981,
  .cx 972 980]
private def block2200 : List Gate := [
  .ccx 1613 980 972,
  .cx 972 980,
  .cx 971 979,
  .ccx 1613 979 971,
  .cx 971 979,
  .cx 970 978,
  .ccx 1613 978 970,
  .cx 970 978]
private def block2208 : List Gate := [
  .cx 969 977,
  .ccx 1613 977 969,
  .cx 969 977,
  .cx 968 976,
  .ccx 1613 976 968,
  .cx 968 976,
  .cx 967 975,
  .ccx 1613 975 967,
  .cx 967 975,
  .cx 966 974,
  .ccx 1613 974 966,
  .cx 966 974,
  .cx 965 973,
  .ccx 1613 973 965,
  .cx 965 973,
  .cx 964 972,
  .ccx 1613 972 964,
  .cx 964 972,
  .cx 963 971,
  .ccx 1613 971 963,
  .cx 963 971,
  .cx 962 970,
  .ccx 1613 970 962,
  .cx 962 970,
  .cx 961 969,
  .ccx 1613 969 961,
  .cx 961 969,
  .cx 960 968,
  .ccx 1613 968 960,
  .cx 960 968,
  .cx 959 967,
  .ccx 1613 967 959]
private def block2240 : List Gate := [
  .cx 959 967,
  .cx 958 966,
  .ccx 1613 966 958,
  .cx 958 966,
  .cx 957 965,
  .ccx 1613 965 957,
  .cx 957 965,
  .cx 956 964,
  .ccx 1613 964 956,
  .cx 956 964,
  .cx 955 963,
  .ccx 1613 963 955,
  .cx 955 963,
  .cx 954 962,
  .ccx 1613 962 954,
  .cx 954 962,
  .cx 953 961,
  .ccx 1613 961 953,
  .cx 953 961,
  .cx 952 960,
  .ccx 1613 960 952,
  .cx 952 960]
private def block2262 : List Gate := [
  .cx 951 959,
  .ccx 1613 959 951,
  .cx 951 959,
  .cx 950 958,
  .ccx 1613 958 950,
  .cx 950 958,
  .cx 949 957,
  .ccx 1613 957 949,
  .cx 949 957,
  .cx 948 956,
  .ccx 1613 956 948,
  .cx 948 956,
  .cx 947 955,
  .ccx 1613 955 947,
  .cx 947 955,
  .cx 946 954,
  .ccx 1613 954 946,
  .cx 946 954]
private def block2280 : List Gate := [
  .cx 945 953,
  .ccx 1613 953 945,
  .cx 945 953,
  .cx 944 952,
  .ccx 1613 952 944,
  .cx 944 952,
  .cx 943 951,
  .ccx 1613 951 943,
  .cx 943 951,
  .cx 942 950,
  .ccx 1613 950 942,
  .cx 942 950,
  .cx 941 949,
  .ccx 1613 949 941,
  .cx 941 949,
  .cx 940 948,
  .ccx 1613 948 940,
  .cx 940 948,
  .cx 939 947,
  .ccx 1613 947 939,
  .cx 939 947,
  .cx 938 946,
  .ccx 1613 946 938,
  .cx 938 946]
private def block2304 : List Gate := [
  .cx 937 945,
  .ccx 1613 945 937,
  .cx 937 945,
  .cx 936 944,
  .ccx 1613 944 936,
  .cx 936 944,
  .cx 935 943,
  .ccx 1613 943 935,
  .cx 935 943,
  .cx 934 942,
  .ccx 1613 942 934,
  .cx 934 942,
  .cx 1705 941,
  .ccx 1613 941 1705,
  .cx 1705 941,
  .cx 1704 940]
private def block2320 : List Gate := [
  .ccx 1613 940 1704,
  .cx 1704 940,
  .cx 1703 939,
  .ccx 1613 939 1703,
  .cx 1703 939,
  .cx 1569 1613,
  .cx 1570 1613,
  .cx 1571 1613,
  .cx 1572 1613,
  .cx 1573 1613,
  .cx 1574 1613,
  .cx 1575 1613,
  .cx 1560 1613,
  .x 1613,
  .cx 1597 1613,
  .ccx 1576 1709 416,
  .ccx 1576 1613 417,
  .ccx 1562 1709 417,
  .ccx 1562 1613 418,
  .ccx 1563 1709 418,
  .ccx 1563 1613 419,
  .ccx 1564 1709 419,
  .ccx 1564 1613 420,
  .ccx 1565 1709 420,
  .ccx 1565 1613 421,
  .ccx 1566 1709 421,
  .ccx 1566 1613 422,
  .ccx 1567 1709 422,
  .ccx 1567 1613 423,
  .ccx 1568 1709 423,
  .ccx 1568 1613 424,
  .ccx 1569 1709 424,
  .ccx 1569 1613 425,
  .ccx 1570 1709 425,
  .ccx 1570 1613 426,
  .ccx 1571 1709 426,
  .ccx 1571 1613 427,
  .ccx 1572 1709 427]
private def block2358 : List Gate := [
  .ccx 1572 1613 428,
  .ccx 1573 1709 428]
private def block2360 : List Gate := [
  .ccx 1573 1613 429,
  .ccx 1574 1709 429,
  .ccx 1574 1613 430,
  .ccx 1575 1709 430,
  .ccx 1575 1613 431,
  .ccx 1560 1709 431,
  .ccx 1560 1613 432,
  .cx 1576 1614,
  .cx 1703 416,
  .ccx 1614 416 1703,
  .cx 1562 1614,
  .cx 1704 417,
  .ccx 1614 417 1704,
  .cx 1563 1614,
  .cx 1705 418,
  .ccx 1614 418 1705,
  .cx 1564 1614,
  .cx 934 419,
  .ccx 1614 419 934,
  .cx 1565 1614,
  .cx 935 420,
  .ccx 1614 420 935,
  .cx 1566 1614,
  .cx 936 421,
  .ccx 1614 421 936,
  .cx 1567 1614,
  .cx 937 422,
  .ccx 1614 422 937,
  .cx 1568 1614,
  .cx 938 423,
  .ccx 1614 423 938,
  .cx 1569 1614,
  .cx 939 424,
  .ccx 1614 424 939,
  .cx 1570 1614,
  .cx 940 425,
  .ccx 1614 425 940,
  .cx 1571 1614,
  .cx 426 941,
  .cx 941 426]
private def block2400 : List Gate := [
  .ccx 1614 941 426,
  .cx 1572 1614,
  .cx 427 942,
  .cx 942 427,
  .ccx 1614 942 427,
  .cx 1573 1614,
  .cx 428 943,
  .cx 943 428,
  .ccx 1614 943 428,
  .cx 1574 1614,
  .cx 429 944,
  .cx 944 429,
  .ccx 1614 944 429,
  .cx 1575 1614,
  .cx 430 945,
  .cx 945 430,
  .ccx 1614 945 430,
  .cx 1560 1614,
  .cx 431 946,
  .cx 946 431,
  .ccx 1614 946 431,
  .cx 432 947,
  .cx 947 432,
  .ccx 1614 947 432,
  .cx 433 948,
  .cx 948 433,
  .ccx 1614 948 433,
  .cx 1560 1614,
  .cx 1575 1614,
  .cx 1574 1614,
  .cx 1573 1614,
  .cx 1572 1614,
  .cx 1571 1614,
  .cx 1570 1614,
  .cx 1569 1614,
  .cx 1568 1614,
  .cx 1567 1614,
  .cx 1566 1614,
  .cx 1565 1614,
  .cx 1564 1614]
private def block2440 : List Gate := [
  .cx 1563 1614,
  .cx 1562 1614,
  .cx 1576 1614,
  .cx 1597 1613,
  .x 1613,
  .pop 1709 1596 1597,
  .cx 1589 1596,
  .cx 1590 1596,
  .cx 1591 1596,
  .cx 1592 1596,
  .cx 1593 1596,
  .cx 1594 1596,
  .cx 1595 1596,
  .cx 1569 1596]
private def block2454 : List Gate := [
  .cx 1570 1596,
  .cx 1571 1596,
  .cx 1572 1596,
  .cx 1573 1596,
  .cx 1574 1596,
  .cx 1575 1596,
  .cx 1560 1596,
  .pop 1568 285 1595,
  .pop 1567 1578 1594,
  .pop 1566 1580 1593,
  .pop 1565 1582 1592,
  .pop 1564 1584 1591,
  .pop 1563 1586 1590,
  .pop 1562 1588 1589,
  .pop 273 1587 1588,
  .pop 274 1586 1587,
  .pop 275 1585 1586,
  .pop 276 1584 1585,
  .pop 277 1583 1584,
  .pop 278 1582 1583,
  .pop 279 1581 1582,
  .pop 280 1580 1581,
  .pop 281 1579 1580,
  .pop 282 1578 1579,
  .pop 283 1577 1578,
  .pop 284 285 1577]
private def block2480 : List Gate := [
  .cx 1559 1576,
  .cx 1561 1576,
  .cx 1575 1560,
  .pop 1560 1800 1575,
  .cx 1574 1560,
  .pop 1560 1801 1574,
  .cx 1573 1560,
  .pop 1560 1802 1573,
  .cx 1572 1560,
  .pop 1560 1803 1572,
  .cx 1571 1560,
  .pop 1560 1804 1571,
  .cx 1570 1560,
  .pop 1560 1805 1570,
  .cx 1569 1560,
  .pop 1560 1806 1569]
private def block2496 : List Gate := [
  .cx 1568 1560,
  .pop 1560 1807 1568,
  .cx 1567 1560,
  .pop 1560 1808 1567,
  .cx 1566 1560,
  .pop 1560 1809 1566,
  .cx 1565 1560,
  .pop 1560 1810 1565,
  .cx 1564 1560,
  .pop 1560 1811 1564,
  .cx 1563 1560,
  .pop 1560 1812 1563,
  .cx 1562 1560,
  .pop 1560 1300 1562,
  .cx 1561 1560,
  .pop 1560 1299 1561,
  .cx 1706 1560,
  .cx 1559 1560,
  .pop 1706 1707 1559]
private theorem check2496 : bitCheck block2496 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff80002ffffefe000 <<< 1556) := by decide +kernel
private def suffix2496 := block2496 ++ ([]:List Gate)
private theorem valid2496 : bitCheck suffix2496 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff80002ffffefe000 <<< 1556) := bit_join block2496 ([]:List Gate) _ (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) _ check2496 rfl
private theorem check2480 : bitCheck block2480 (0xfffffffffffffffffff80002ffffefe000 <<< 1556) = some (0xfffffffffffffffffff80002ffffe00000 <<< 1556) := by decide +kernel
private def suffix2480 := block2480 ++ suffix2496
private theorem valid2480 : bitCheck suffix2480 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff80002ffffe00000 <<< 1556) := bit_join block2480 suffix2496 _ (0xfffffffffffffffffff80002ffffefe000 <<< 1556) _ check2480 valid2496
private theorem check2454 : bitCheck block2454 (0xfffffffffffffffffff80002ffffe00000 <<< 1556) = some (0xfffffffffffffffffff800020000000000 <<< 1556) := by decide +kernel
private def suffix2454 := block2454 ++ suffix2480
private theorem valid2454 : bitCheck suffix2454 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800020000000000 <<< 1556) := bit_join block2454 suffix2480 _ (0xfffffffffffffffffff80002ffffe00000 <<< 1556) _ check2454 valid2480
private theorem check2440 : bitCheck block2440 (0xfffffffffffffffffff800020000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2440 := block2440 ++ suffix2454
private theorem valid2440 : bitCheck suffix2440 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2440 suffix2454 _ (0xfffffffffffffffffff800020000000000 <<< 1556) _ check2440 valid2454
private theorem check2400 : bitCheck block2400 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2400 := block2400 ++ suffix2440
private theorem valid2400 : bitCheck suffix2400 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2400 suffix2440 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2400 valid2440
private theorem check2360 : bitCheck block2360 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2360 := block2360 ++ suffix2400
private theorem valid2360 : bitCheck suffix2360 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2360 suffix2400 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2360 valid2400
private theorem check2358 : bitCheck block2358 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2358 := block2358 ++ suffix2360
private theorem valid2358 : bitCheck suffix2358 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2358 suffix2360 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2358 valid2360
private theorem check2320 : bitCheck block2320 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2320 := block2320 ++ suffix2358
private theorem valid2320 : bitCheck suffix2320 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2320 suffix2358 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2320 valid2358
private theorem check2304 : bitCheck block2304 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2304 := block2304 ++ suffix2320
private theorem valid2304 : bitCheck suffix2304 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2304 suffix2320 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2304 valid2320
private theorem check2280 : bitCheck block2280 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2280 := block2280 ++ suffix2304
private theorem valid2280 : bitCheck suffix2280 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2280 suffix2304 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2280 valid2304
private theorem check2262 : bitCheck block2262 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2262 := block2262 ++ suffix2280
private theorem valid2262 : bitCheck suffix2262 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2262 suffix2280 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2262 valid2280
private theorem check2240 : bitCheck block2240 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2240 := block2240 ++ suffix2262
private theorem valid2240 : bitCheck suffix2240 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2240 suffix2262 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2240 valid2262
private theorem check2208 : bitCheck block2208 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2208 := block2208 ++ suffix2240
private theorem valid2208 : bitCheck suffix2208 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2208 suffix2240 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2208 valid2240
private theorem check2200 : bitCheck block2200 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2200 := block2200 ++ suffix2208
private theorem valid2200 : bitCheck suffix2200 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2200 suffix2208 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2200 valid2208
private theorem check2166 : bitCheck block2166 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2166 := block2166 ++ suffix2200
private theorem valid2166 : bitCheck suffix2166 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2166 suffix2200 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2166 valid2200
private theorem check2160 : bitCheck block2160 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2160 := block2160 ++ suffix2166
private theorem valid2160 : bitCheck suffix2160 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2160 suffix2166 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2160 valid2166
private theorem check2120 : bitCheck block2120 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2120 := block2120 ++ suffix2160
private theorem valid2120 : bitCheck suffix2120 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2120 suffix2160 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2120 valid2160
private theorem check2112 : bitCheck block2112 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2112 := block2112 ++ suffix2120
private theorem valid2112 : bitCheck suffix2112 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2112 suffix2120 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2112 valid2120
private theorem check2080 : bitCheck block2080 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2080 := block2080 ++ suffix2112
private theorem valid2080 : bitCheck suffix2080 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2080 suffix2112 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2080 valid2112
private theorem check2070 : bitCheck block2070 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2070 := block2070 ++ suffix2080
private theorem valid2070 : bitCheck suffix2070 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2070 suffix2080 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2070 valid2080
private theorem check2040 : bitCheck block2040 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2040 := block2040 ++ suffix2070
private theorem valid2040 : bitCheck suffix2040 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2040 suffix2070 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2040 valid2070
private theorem check2016 : bitCheck block2016 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2016 := block2016 ++ suffix2040
private theorem valid2016 : bitCheck suffix2016 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2016 suffix2040 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2016 valid2040
private theorem check2000 : bitCheck block2000 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix2000 := block2000 ++ suffix2016
private theorem valid2000 : bitCheck suffix2000 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block2000 suffix2016 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check2000 valid2016
private theorem check1974 : bitCheck block1974 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1974 := block1974 ++ suffix2000
private theorem valid1974 : bitCheck suffix1974 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1974 suffix2000 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1974 valid2000
private theorem check1960 : bitCheck block1960 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1960 := block1960 ++ suffix1974
private theorem valid1960 : bitCheck suffix1960 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1960 suffix1974 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1960 valid1974
private theorem check1920 : bitCheck block1920 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1920 := block1920 ++ suffix1960
private theorem valid1920 : bitCheck suffix1920 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1920 suffix1960 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1920 valid1960
private theorem check1880 : bitCheck block1880 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1880 := block1880 ++ suffix1920
private theorem valid1880 : bitCheck suffix1880 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1880 suffix1920 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1880 valid1920
private theorem check1878 : bitCheck block1878 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1878 := block1878 ++ suffix1880
private theorem valid1878 : bitCheck suffix1878 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1878 suffix1880 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1878 valid1880
private theorem check1840 : bitCheck block1840 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1840 := block1840 ++ suffix1878
private theorem valid1840 : bitCheck suffix1840 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1840 suffix1878 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1840 valid1878
private theorem check1824 : bitCheck block1824 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1824 := block1824 ++ suffix1840
private theorem valid1824 : bitCheck suffix1824 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1824 suffix1840 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1824 valid1840
private theorem check1800 : bitCheck block1800 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1800 := block1800 ++ suffix1824
private theorem valid1800 : bitCheck suffix1800 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1800 suffix1824 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1800 valid1824
private theorem check1782 : bitCheck block1782 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1782 := block1782 ++ suffix1800
private theorem valid1782 : bitCheck suffix1782 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1782 suffix1800 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1782 valid1800
private theorem check1760 : bitCheck block1760 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1760 := block1760 ++ suffix1782
private theorem valid1760 : bitCheck suffix1760 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1760 suffix1782 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1760 valid1782
private theorem check1728 : bitCheck block1728 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1728 := block1728 ++ suffix1760
private theorem valid1728 : bitCheck suffix1728 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1728 suffix1760 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1728 valid1760
private theorem check1720 : bitCheck block1720 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1720 := block1720 ++ suffix1728
private theorem valid1720 : bitCheck suffix1720 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1720 suffix1728 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1720 valid1728
private theorem check1686 : bitCheck block1686 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1686 := block1686 ++ suffix1720
private theorem valid1686 : bitCheck suffix1686 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1686 suffix1720 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1686 valid1720
private theorem check1680 : bitCheck block1680 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1680 := block1680 ++ suffix1686
private theorem valid1680 : bitCheck suffix1680 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1680 suffix1686 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1680 valid1686
private theorem check1640 : bitCheck block1640 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1640 := block1640 ++ suffix1680
private theorem valid1640 : bitCheck suffix1640 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1640 suffix1680 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1640 valid1680
private theorem check1632 : bitCheck block1632 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1632 := block1632 ++ suffix1640
private theorem valid1632 : bitCheck suffix1632 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1632 suffix1640 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1632 valid1640
private theorem check1600 : bitCheck block1600 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1600 := block1600 ++ suffix1632
private theorem valid1600 : bitCheck suffix1600 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1600 suffix1632 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1600 valid1632
private theorem check1590 : bitCheck block1590 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1590 := block1590 ++ suffix1600
private theorem valid1590 : bitCheck suffix1590 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1590 suffix1600 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1590 valid1600
private theorem check1560 : bitCheck block1560 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1560 := block1560 ++ suffix1590
private theorem valid1560 : bitCheck suffix1560 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1560 suffix1590 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1560 valid1590
private theorem check1536 : bitCheck block1536 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1536 := block1536 ++ suffix1560
private theorem valid1536 : bitCheck suffix1536 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1536 suffix1560 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1536 valid1560
private theorem check1520 : bitCheck block1520 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1520 := block1520 ++ suffix1536
private theorem valid1520 : bitCheck suffix1520 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1520 suffix1536 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1520 valid1536
private theorem check1494 : bitCheck block1494 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1494 := block1494 ++ suffix1520
private theorem valid1494 : bitCheck suffix1494 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1494 suffix1520 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1494 valid1520
private theorem check1480 : bitCheck block1480 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1480 := block1480 ++ suffix1494
private theorem valid1480 : bitCheck suffix1480 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1480 suffix1494 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1480 valid1494
private theorem check1440 : bitCheck block1440 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1440 := block1440 ++ suffix1480
private theorem valid1440 : bitCheck suffix1440 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1440 suffix1480 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1440 valid1480
private theorem check1400 : bitCheck block1400 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1400 := block1400 ++ suffix1440
private theorem valid1400 : bitCheck suffix1400 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1400 suffix1440 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1400 valid1440
private theorem check1398 : bitCheck block1398 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1398 := block1398 ++ suffix1400
private theorem valid1398 : bitCheck suffix1398 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1398 suffix1400 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1398 valid1400
private theorem check1360 : bitCheck block1360 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1360 := block1360 ++ suffix1398
private theorem valid1360 : bitCheck suffix1360 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1360 suffix1398 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1360 valid1398
private theorem check1344 : bitCheck block1344 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1344 := block1344 ++ suffix1360
private theorem valid1344 : bitCheck suffix1344 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1344 suffix1360 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1344 valid1360
private theorem check1320 : bitCheck block1320 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1320 := block1320 ++ suffix1344
private theorem valid1320 : bitCheck suffix1320 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1320 suffix1344 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1320 valid1344
private theorem check1302 : bitCheck block1302 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1302 := block1302 ++ suffix1320
private theorem valid1302 : bitCheck suffix1302 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1302 suffix1320 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1302 valid1320
private theorem check1280 : bitCheck block1280 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1280 := block1280 ++ suffix1302
private theorem valid1280 : bitCheck suffix1280 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1280 suffix1302 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1280 valid1302
private theorem check1248 : bitCheck block1248 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1248 := block1248 ++ suffix1280
private theorem valid1248 : bitCheck suffix1248 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1248 suffix1280 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1248 valid1280
private theorem check1240 : bitCheck block1240 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1240 := block1240 ++ suffix1248
private theorem valid1240 : bitCheck suffix1240 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1240 suffix1248 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1240 valid1248
private theorem check1206 : bitCheck block1206 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1206 := block1206 ++ suffix1240
private theorem valid1206 : bitCheck suffix1206 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1206 suffix1240 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1206 valid1240
private theorem check1200 : bitCheck block1200 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1200 := block1200 ++ suffix1206
private theorem valid1200 : bitCheck suffix1200 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1200 suffix1206 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1200 valid1206
private theorem check1160 : bitCheck block1160 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1160 := block1160 ++ suffix1200
private theorem valid1160 : bitCheck suffix1160 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1160 suffix1200 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1160 valid1200
private theorem check1152 : bitCheck block1152 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1152 := block1152 ++ suffix1160
private theorem valid1152 : bitCheck suffix1152 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1152 suffix1160 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1152 valid1160
private theorem check1120 : bitCheck block1120 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1120 := block1120 ++ suffix1152
private theorem valid1120 : bitCheck suffix1120 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1120 suffix1152 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1120 valid1152
private theorem check1110 : bitCheck block1110 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1110 := block1110 ++ suffix1120
private theorem valid1110 : bitCheck suffix1110 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1110 suffix1120 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1110 valid1120
private theorem check1080 : bitCheck block1080 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1080 := block1080 ++ suffix1110
private theorem valid1080 : bitCheck suffix1080 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1080 suffix1110 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1080 valid1110
private theorem check1056 : bitCheck block1056 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1056 := block1056 ++ suffix1080
private theorem valid1056 : bitCheck suffix1056 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1056 suffix1080 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1056 valid1080
private theorem check1040 : bitCheck block1040 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1040 := block1040 ++ suffix1056
private theorem valid1040 : bitCheck suffix1040 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1040 suffix1056 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1040 valid1056
private theorem check1014 : bitCheck block1014 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1014 := block1014 ++ suffix1040
private theorem valid1014 : bitCheck suffix1014 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1014 suffix1040 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1014 valid1040
private theorem check1000 : bitCheck block1000 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix1000 := block1000 ++ suffix1014
private theorem valid1000 : bitCheck suffix1000 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block1000 suffix1014 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check1000 valid1014
private theorem check960 : bitCheck block960 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix960 := block960 ++ suffix1000
private theorem valid960 : bitCheck suffix960 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block960 suffix1000 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check960 valid1000
private theorem check920 : bitCheck block920 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix920 := block920 ++ suffix960
private theorem valid920 : bitCheck suffix920 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block920 suffix960 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check920 valid960
private theorem check918 : bitCheck block918 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix918 := block918 ++ suffix920
private theorem valid918 : bitCheck suffix918 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block918 suffix920 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check918 valid920
private theorem check880 : bitCheck block880 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix880 := block880 ++ suffix918
private theorem valid880 : bitCheck suffix880 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block880 suffix918 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check880 valid918
private theorem check864 : bitCheck block864 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix864 := block864 ++ suffix880
private theorem valid864 : bitCheck suffix864 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block864 suffix880 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check864 valid880
private theorem check840 : bitCheck block840 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix840 := block840 ++ suffix864
private theorem valid840 : bitCheck suffix840 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block840 suffix864 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check840 valid864
private theorem check822 : bitCheck block822 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix822 := block822 ++ suffix840
private theorem valid822 : bitCheck suffix822 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block822 suffix840 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check822 valid840
private theorem check800 : bitCheck block800 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix800 := block800 ++ suffix822
private theorem valid800 : bitCheck suffix800 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block800 suffix822 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check800 valid822
private theorem check768 : bitCheck block768 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix768 := block768 ++ suffix800
private theorem valid768 : bitCheck suffix768 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block768 suffix800 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check768 valid800
private theorem check760 : bitCheck block760 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := by decide +kernel
private def suffix760 := block760 ++ suffix768
private theorem valid760 : bitCheck suffix760 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffffffffffff800000000000000 <<< 1556) := bit_join block760 suffix768 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check760 valid768
private theorem check726 : bitCheck block726 (0xfffffffffffffffffff800000000000000 <<< 1556) = some (0xffffffffffffffffe00000000000000000 <<< 1556) := by decide +kernel
private def suffix726 := block726 ++ suffix760
private theorem valid726 : bitCheck suffix726 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffffffffffffffe00000000000000000 <<< 1556) := bit_join block726 suffix760 _ (0xfffffffffffffffffff800000000000000 <<< 1556) _ check726 valid760
private theorem check720 : bitCheck block720 (0xffffffffffffffffe00000000000000000 <<< 1556) = some (0xffffffffffffffff000000000000000000 <<< 1556) := by decide +kernel
private def suffix720 := block720 ++ suffix726
private theorem valid720 : bitCheck suffix720 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffffffffffffff000000000000000000 <<< 1556) := bit_join block720 suffix726 _ (0xffffffffffffffffe00000000000000000 <<< 1556) _ check720 valid726
private theorem check680 : bitCheck block680 (0xffffffffffffffff000000000000000000 <<< 1556) = some (0xfffffffffff00000000000000000000000 <<< 1556) := by decide +kernel
private def suffix680 := block680 ++ suffix720
private theorem valid680 : bitCheck suffix680 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xfffffffffff00000000000000000000000 <<< 1556) := bit_join block680 suffix720 _ (0xffffffffffffffff000000000000000000 <<< 1556) _ check680 valid720
private theorem check672 : bitCheck block672 (0xfffffffffff00000000000000000000000 <<< 1556) = some (0xffffffffff000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix672 := block672 ++ suffix680
private theorem valid672 : bitCheck suffix672 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffffffff000000000000000000000000 <<< 1556) := bit_join block672 suffix680 _ (0xfffffffffff00000000000000000000000 <<< 1556) _ check672 valid680
private theorem check640 : bitCheck block640 (0xffffffffff000000000000000000000000 <<< 1556) = some (0xffffff0000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix640 := block640 ++ suffix672
private theorem valid640 : bitCheck suffix640 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffff0000000000000000000000000000 <<< 1556) := bit_join block640 suffix672 _ (0xffffffffff000000000000000000000000 <<< 1556) _ check640 valid672
private theorem check630 : bitCheck block630 (0xffffff0000000000000000000000000000 <<< 1556) = some (0xffffe00000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix630 := block630 ++ suffix640
private theorem valid630 : bitCheck suffix630 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xffffe00000000000000000000000000000 <<< 1556) := bit_join block630 suffix640 _ (0xffffff0000000000000000000000000000 <<< 1556) _ check630 valid640
private theorem check600 : bitCheck block600 (0xffffe00000000000000000000000000000 <<< 1556) = some (0xf000000000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix600 := block600 ++ suffix630
private theorem valid600 : bitCheck suffix600 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0xf000000000000000000000000000000000 <<< 1556) := bit_join block600 suffix630 _ (0xffffe00000000000000000000000000000 <<< 1556) _ check600 valid630
private theorem check576 : bitCheck block576 (0xf000000000000000000000000000000000 <<< 1556) = some 0 := by decide +kernel
private def suffix576 := block576 ++ suffix600
private theorem valid576 : bitCheck suffix576 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some 0 := bit_join block576 suffix600 _ (0xf000000000000000000000000000000000 <<< 1556) _ check576 valid600
private theorem check560 : bitCheck block560 0 = some 0 := by decide +kernel
private def suffix560 := block560 ++ suffix576
private theorem valid560 : bitCheck suffix560 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some 0 := bit_join block560 suffix576 _ 0 _ check560 valid576
private theorem check534 : bitCheck block534 0 = some (0x7e007fffc00000000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix534 := block534 ++ suffix560
private theorem valid534 : bitCheck suffix534 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffc00000000000000000000000000000000 <<< 1556) := bit_join block534 suffix560 _ 0 _ check534 valid560
private theorem check520 : bitCheck block520 (0x7e007fffc00000000000000000000000000000000 <<< 1556) = some (0x7e007fffffff00000000000000000000000000000 <<< 1556) := by decide +kernel
private def suffix520 := block520 ++ suffix534
private theorem valid520 : bitCheck suffix520 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffff00000000000000000000000000000 <<< 1556) := bit_join block520 suffix534 _ (0x7e007fffc00000000000000000000000000000000 <<< 1556) _ check520 valid534
private theorem check480 : bitCheck block480 (0x7e007fffffff00000000000000000000000000000 <<< 1556) = some (0x7e007fffffffffffffffff0000000000000000000 <<< 1556) := by decide +kernel
private def suffix480 := block480 ++ suffix520
private theorem valid480 : bitCheck suffix480 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffff0000000000000000000 <<< 1556) := bit_join block480 suffix520 _ (0x7e007fffffff00000000000000000000000000000 <<< 1556) _ check480 valid520
private theorem check440 : bitCheck block440 (0x7e007fffffffffffffffff0000000000000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix440 := block440 ++ suffix480
private theorem valid440 : bitCheck suffix440 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block440 suffix480 _ (0x7e007fffffffffffffffff0000000000000000000 <<< 1556) _ check440 valid480
private theorem check438 : bitCheck block438 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix438 := block438 ++ suffix440
private theorem valid438 : bitCheck suffix438 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block438 suffix440 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check438 valid440
private theorem check400 : bitCheck block400 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix400 := block400 ++ suffix438
private theorem valid400 : bitCheck suffix400 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block400 suffix438 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check400 valid438
private theorem check384 : bitCheck block384 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix384 := block384 ++ suffix400
private theorem valid384 : bitCheck suffix384 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block384 suffix400 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check384 valid400
private theorem check360 : bitCheck block360 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix360 := block360 ++ suffix384
private theorem valid360 : bitCheck suffix360 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block360 suffix384 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check360 valid384
private theorem check342 : bitCheck block342 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := by decide +kernel
private def suffix342 := block342 ++ suffix360
private theorem valid342 : bitCheck suffix342 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) := bit_join block342 suffix360 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check342 valid360
private theorem check320 : bitCheck block320 (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffe0000000000 <<< 1556) := by decide +kernel
private def suffix320 := block320 ++ suffix342
private theorem valid320 : bitCheck suffix320 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffe0000000000 <<< 1556) := bit_join block320 suffix342 _ (0x7e007fffffffffffffffffffffffffc0000000000 <<< 1556) _ check320 valid342
private theorem check288 : bitCheck block288 (0x7e007fffffffffffffffffffffffffe0000000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffefffc000000 <<< 1556) := by decide +kernel
private def suffix288 := block288 ++ suffix320
private theorem valid288 : bitCheck suffix288 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffefffc000000 <<< 1556) := bit_join block288 suffix320 _ (0x7e007fffffffffffffffffffffffffe0000000000 <<< 1556) _ check288 valid320
private theorem check280 : bitCheck block280 (0x7e007fffffffffffffffffffffffffefffc000000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffe00000 <<< 1556) := by decide +kernel
private def suffix280 := block280 ++ suffix288
private theorem valid280 : bitCheck suffix280 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffe00000 <<< 1556) := bit_join block280 suffix288 _ (0x7e007fffffffffffffffffffffffffefffc000000 <<< 1556) _ check280 valid288
private theorem check246 : bitCheck block246 (0x7e007fffffffffffffffffffffffffeffffe00000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffefffc0 <<< 1556) := by decide +kernel
private def suffix246 := block246 ++ suffix280
private theorem valid246 : bitCheck suffix246 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffefffc0 <<< 1556) := bit_join block246 suffix280 _ (0x7e007fffffffffffffffffffffffffeffffe00000 <<< 1556) _ check246 valid280
private theorem check240 : bitCheck block240 (0x7e007fffffffffffffffffffffffffeffffefffc0 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffefffe8 <<< 1556) := by decide +kernel
private def suffix240 := block240 ++ suffix246
private theorem valid240 : bitCheck suffix240 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffefffe8 <<< 1556) := bit_join block240 suffix246 _ (0x7e007fffffffffffffffffffffffffeffffefffc0 <<< 1556) _ check240 valid246
private theorem check200 : bitCheck block200 (0x7e007fffffffffffffffffffffffffeffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffef8000 <<< 1556) := by decide +kernel
private def suffix200 := block200 ++ suffix240
private theorem valid200 : bitCheck suffix200 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffef8000 <<< 1556) := bit_join block200 suffix240 _ (0x7e007fffffffffffffffffffffffffeffffefffe8 <<< 1556) _ check200 valid240
private theorem check192 : bitCheck block192 (0x7e007fffffffffffffffffffffffffeffffef8000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffe80000 <<< 1556) := by decide +kernel
private def suffix192 := block192 ++ suffix200
private theorem valid192 : bitCheck suffix192 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffe80000 <<< 1556) := bit_join block192 suffix200 _ (0x7e007fffffffffffffffffffffffffeffffef8000 <<< 1556) _ check192 valid200
private theorem check160 : bitCheck block160 (0x7e007fffffffffffffffffffffffffeffffe80000 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) := by decide +kernel
private def suffix160 := block160 ++ suffix192
private theorem valid160 : bitCheck suffix160 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) := bit_join block160 suffix192 _ (0x7e007fffffffffffffffffffffffffeffffe80000 <<< 1556) _ check160 valid192
private theorem check150 : bitCheck block150 (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) := by decide +kernel
private def suffix150 := block150 ++ suffix160
private theorem valid150 : bitCheck suffix150 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) := bit_join block150 suffix160 _ (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) _ check150 valid160
private theorem check120 : bitCheck block120 (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffe00 <<< 1556) := by decide +kernel
private def suffix120 := block120 ++ suffix150
private theorem valid120 : bitCheck suffix120 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffe00 <<< 1556) := bit_join block120 suffix150 _ (0x7e007fffffffffffffffffffffffffeffffeffffc <<< 1556) _ check120 valid150
private theorem check96 : bitCheck block96 (0x7e007fffffffffffffffffffffffffeffffeffe00 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix96 := block96 ++ suffix120
private theorem valid96 : bitCheck suffix96 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block96 suffix120 _ (0x7e007fffffffffffffffffffffffffeffffeffe00 <<< 1556) _ check96 valid120
private theorem check80 : bitCheck block80 (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix80 := block80 ++ suffix96
private theorem valid80 : bitCheck suffix80 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block80 suffix96 _ (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check80 valid96
private theorem check54 : bitCheck block54 (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix54 := block54 ++ suffix80
private theorem valid54 : bitCheck suffix54 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block54 suffix80 _ (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check54 valid80
private theorem check40 : bitCheck block40 (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix40 := block40 ++ suffix54
private theorem valid40 : bitCheck suffix40 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block40 suffix54 _ (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check40 valid54
private theorem check0 : bitCheck block0 (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := by decide +kernel
private def suffix0 := block0 ++ suffix40
private theorem valid0 : bitCheck suffix0 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := bit_join block0 suffix40 _ (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) _ check0 valid40
private def group0 := suffix0
private theorem cert0 : bitCheck group0 (0xfffffffffffffffffff80002ffffefffe8 <<< 1556) = some (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556) := valid0
private def ops := group0 ++ (group1 ++ group2)
private theorem fPart0 : Partial.leave255Part0 = GateMirror.forward block0 ++ GateMirror.forward block40 ++ GateMirror.forward block54 ++ GateMirror.forward block80 := by rfl
private theorem fPart1 : Partial.leave255Part1 = GateMirror.forward block96 ++ GateMirror.forward block120 ++ GateMirror.forward block150 ++ GateMirror.forward block160 := by rfl
private theorem fPart2 : Partial.leave255Part2 = GateMirror.forward block192 ++ GateMirror.forward block200 ++ GateMirror.forward block240 ++ GateMirror.forward block246 ++ GateMirror.forward block280 := by rfl
private theorem fPart3 : Partial.leave255Part3 = GateMirror.forward block288 ++ GateMirror.forward block320 ++ GateMirror.forward block342 ++ GateMirror.forward block360 := by rfl
private theorem fPart4 : Partial.leave255Part4 = GateMirror.forward block384 ++ GateMirror.forward block400 ++ GateMirror.forward block438 ++ GateMirror.forward block440 := by rfl
private theorem fPart5 : Partial.leave255Part5 = GateMirror.forward block480 ++ GateMirror.forward block520 ++ GateMirror.forward block534 ++ GateMirror.forward block560 := by rfl
private theorem fPart6 : Partial.leave255Part6 = GateMirror.forward block576 ++ GateMirror.forward block600 ++ GateMirror.forward block630 ++ GateMirror.forward block640 := by rfl
private theorem fPart7 : Partial.leave255Part7 = GateMirror.forward block672 ++ GateMirror.forward block680 ++ GateMirror.forward block720 ++ GateMirror.forward block726 ++ GateMirror.forward block760 := by rfl
private theorem fPart8 : Partial.leave255Part8 = GateMirror.forward block768 ++ GateMirror.forward block800 ++ GateMirror.forward block822 ++ GateMirror.forward block840 := by rfl
private theorem fPart9 : Partial.leave255Part9 = GateMirror.forward block864 ++ GateMirror.forward block880 ++ GateMirror.forward block918 ++ GateMirror.forward block920 := by rfl
private theorem fPart10 : Partial.leave255Part10 = GateMirror.forward block960 ++ GateMirror.forward block1000 ++ GateMirror.forward block1014 ++ GateMirror.forward block1040 := by rfl
private theorem fPart11 : Partial.leave255Part11 = GateMirror.forward block1056 ++ GateMirror.forward block1080 ++ GateMirror.forward block1110 ++ GateMirror.forward block1120 := by rfl
private theorem fPart12 : Partial.leave255Part12 = GateMirror.forward block1152 ++ GateMirror.forward block1160 ++ GateMirror.forward block1200 ++ GateMirror.forward block1206 ++ GateMirror.forward block1240 := by rfl
private theorem fPart13 : Partial.leave255Part13 = GateMirror.forward block1248 ++ GateMirror.forward block1280 ++ GateMirror.forward block1302 ++ GateMirror.forward block1320 := by rfl
private theorem fPart14 : Partial.leave255Part14 = GateMirror.forward block1344 ++ GateMirror.forward block1360 ++ GateMirror.forward block1398 ++ GateMirror.forward block1400 := by rfl
private theorem fPart15 : Partial.leave255Part15 = GateMirror.forward block1440 ++ GateMirror.forward block1480 ++ GateMirror.forward block1494 ++ GateMirror.forward block1520 := by rfl
private theorem fPart16 : Partial.leave255Part16 = GateMirror.forward block1536 ++ GateMirror.forward block1560 ++ GateMirror.forward block1590 ++ GateMirror.forward block1600 := by rfl
private theorem fPart17 : Partial.leave255Part17 = GateMirror.forward block1632 ++ GateMirror.forward block1640 ++ GateMirror.forward block1680 ++ GateMirror.forward block1686 ++ GateMirror.forward block1720 := by rfl
private theorem fPart18 : Partial.leave255Part18 = GateMirror.forward block1728 ++ GateMirror.forward block1760 ++ GateMirror.forward block1782 ++ GateMirror.forward block1800 := by rfl
private theorem fPart19 : Partial.leave255Part19 = GateMirror.forward block1824 ++ GateMirror.forward block1840 ++ GateMirror.forward block1878 ++ GateMirror.forward block1880 := by rfl
private theorem fPart20 : Partial.leave255Part20 = GateMirror.forward block1920 ++ GateMirror.forward block1960 ++ GateMirror.forward block1974 ++ GateMirror.forward block2000 := by rfl
private theorem fPart21 : Partial.leave255Part21 = GateMirror.forward block2016 ++ GateMirror.forward block2040 ++ GateMirror.forward block2070 ++ GateMirror.forward block2080 := by rfl
private theorem fPart22 : Partial.leave255Part22 = GateMirror.forward block2112 ++ GateMirror.forward block2120 ++ GateMirror.forward block2160 ++ GateMirror.forward block2166 ++ GateMirror.forward block2200 := by rfl
private theorem fPart23 : Partial.leave255Part23 = GateMirror.forward block2208 ++ GateMirror.forward block2240 ++ GateMirror.forward block2262 ++ GateMirror.forward block2280 := by rfl
private theorem fPart24 : Partial.leave255Part24 = GateMirror.forward block2304 ++ GateMirror.forward block2320 ++ GateMirror.forward block2358 ++ GateMirror.forward block2360 := by rfl
private theorem fPart25 : Partial.leave255Part25 = GateMirror.forward block2400 ++ GateMirror.forward block2440 ++ GateMirror.forward block2454 ++ GateMirror.forward block2480 := by rfl
private theorem fPart26 : Partial.leave255Part26 = GateMirror.forward block2496 ++ GateMirror.forward block2515 ++ GateMirror.forward block2550 ++ GateMirror.forward block2555 := by rfl
private theorem fPart27 : Partial.leave255Part27 = GateMirror.forward block2592 ++ GateMirror.forward block2595 ++ GateMirror.forward block2635 ++ GateMirror.forward block2646 ++ GateMirror.forward block2675 := by rfl
private theorem fPart28 : Partial.leave255Part28 = GateMirror.forward block2688 ++ GateMirror.forward block2715 ++ GateMirror.forward block2742 ++ GateMirror.forward block2755 := by rfl
private theorem fPart29 : Partial.leave255Part29 = GateMirror.forward block2784 ++ GateMirror.forward block2795 ++ GateMirror.forward block2835 ++ GateMirror.forward block2838 ++ GateMirror.forward block2875 := by rfl
private theorem fPart30 : Partial.leave255Part30 = GateMirror.forward block2880 ++ GateMirror.forward block2915 ++ GateMirror.forward block2934 ++ GateMirror.forward block2955 := by rfl
private theorem fPart31 : Partial.leave255Part31 = GateMirror.forward block2976 ++ GateMirror.forward block2995 ++ GateMirror.forward block3030 ++ GateMirror.forward block3035 := by rfl
private theorem fPart32 : Partial.leave255Part32 = GateMirror.forward block3072 ++ GateMirror.forward block3075 ++ GateMirror.forward block3115 ++ GateMirror.forward block3126 ++ GateMirror.forward block3155 ++ GateMirror.forward block3162 := by rfl
private theorem fPart33 : Partial.leave255Part33 = GateMirror.forward block3168 ++ GateMirror.forward block3202 ++ GateMirror.forward block3222 ++ GateMirror.forward block3242 := by rfl
private theorem fPart34 : Partial.leave255Part34 = GateMirror.forward block3264 ++ GateMirror.forward block3282 ++ GateMirror.forward block3318 ++ GateMirror.forward block3322 := by rfl
private theorem fPart35 : Partial.leave255Part35 = GateMirror.forward block3360 ++ GateMirror.forward block3362 ++ GateMirror.forward block3402 ++ GateMirror.forward block3414 ++ GateMirror.forward block3442 := by rfl
private theorem fPart36 : Partial.leave255Part36 = GateMirror.forward block3456 ++ GateMirror.forward block3482 := by rfl
private theorem fEq : GateMirror.forward ops = Partial.leave255 := by
  simp only [ops,group0,group1,group2,suffix0,suffix40,suffix54,suffix80,suffix96,suffix120,suffix150,suffix160,suffix192,suffix200,suffix240,suffix246,suffix280,suffix288,suffix320,suffix342,suffix360,suffix384,suffix400,suffix438,suffix440,suffix480,suffix520,suffix534,suffix560,suffix576,suffix600,suffix630,suffix640,suffix672,suffix680,suffix720,suffix726,suffix760,suffix768,suffix800,suffix822,suffix840,suffix864,suffix880,suffix918,suffix920,suffix960,suffix1000,suffix1014,suffix1040,suffix1056,suffix1080,suffix1110,suffix1120,suffix1152,suffix1160,suffix1200,suffix1206,suffix1240,suffix1248,suffix1280,suffix1302,suffix1320,suffix1344,suffix1360,suffix1398,suffix1400,suffix1440,suffix1480,suffix1494,suffix1520,suffix1536,suffix1560,suffix1590,suffix1600,suffix1632,suffix1640,suffix1680,suffix1686,suffix1720,suffix1728,suffix1760,suffix1782,suffix1800,suffix1824,suffix1840,suffix1878,suffix1880,suffix1920,suffix1960,suffix1974,suffix2000,suffix2016,suffix2040,suffix2070,suffix2080,suffix2112,suffix2120,suffix2160,suffix2166,suffix2200,suffix2208,suffix2240,suffix2262,suffix2280,suffix2304,suffix2320,suffix2358,suffix2360,suffix2400,suffix2440,suffix2454,suffix2480,suffix2496,suffix2515,suffix2550,suffix2555,suffix2592,suffix2595,suffix2635,suffix2646,suffix2675,suffix2688,suffix2715,suffix2742,suffix2755,suffix2784,suffix2795,suffix2835,suffix2838,suffix2875,suffix2880,suffix2915,suffix2934,suffix2955,suffix2976,suffix2995,suffix3030,suffix3035,suffix3072,suffix3075,suffix3115,suffix3126,suffix3155,suffix3162,suffix3168,suffix3202,suffix3222,suffix3242,suffix3264,suffix3282,suffix3318,suffix3322,suffix3360,suffix3362,suffix3402,suffix3414,suffix3442,suffix3456,suffix3482,fwAppend,List.append_nil,Partial.leave255,fPart0,fPart1,fPart2,fPart3,fPart4,fPart5,fPart6,fPart7,fPart8,fPart9,fPart10,fPart11,fPart12,fPart13,fPart14,fPart15,fPart16,fPart17,fPart18,fPart19,fPart20,fPart21,fPart22,fPart23,fPart24,fPart25,fPart26,fPart27,fPart28,fPart29,fPart30,fPart31,fPart32,fPart33,fPart34,fPart35,fPart36,List.append_assoc]
private theorem bPart0 : Partial.leave255InvPart0 = GateMirror.inverse block3482 ++ GateMirror.inverse block3456 ++ GateMirror.inverse block3442 ++ GateMirror.inverse block3414 := by rfl
private theorem bPart1 : Partial.leave255InvPart1 = GateMirror.inverse block3402 ++ GateMirror.inverse block3362 ++ GateMirror.inverse block3360 ++ GateMirror.inverse block3322 ++ GateMirror.inverse block3318 := by rfl
private theorem bPart2 : Partial.leave255InvPart2 = GateMirror.inverse block3282 ++ GateMirror.inverse block3264 ++ GateMirror.inverse block3242 ++ GateMirror.inverse block3222 := by rfl
private theorem bPart3 : Partial.leave255InvPart3 = GateMirror.inverse block3202 ++ GateMirror.inverse block3168 ++ GateMirror.inverse block3162 ++ GateMirror.inverse block3155 ++ GateMirror.inverse block3126 := by rfl
private theorem bPart4 : Partial.leave255InvPart4 = GateMirror.inverse block3115 ++ GateMirror.inverse block3075 ++ GateMirror.inverse block3072 ++ GateMirror.inverse block3035 ++ GateMirror.inverse block3030 := by rfl
private theorem bPart5 : Partial.leave255InvPart5 = GateMirror.inverse block2995 ++ GateMirror.inverse block2976 ++ GateMirror.inverse block2955 ++ GateMirror.inverse block2934 := by rfl
private theorem bPart6 : Partial.leave255InvPart6 = GateMirror.inverse block2915 ++ GateMirror.inverse block2880 ++ GateMirror.inverse block2875 ++ GateMirror.inverse block2838 := by rfl
private theorem bPart7 : Partial.leave255InvPart7 = GateMirror.inverse block2835 ++ GateMirror.inverse block2795 ++ GateMirror.inverse block2784 ++ GateMirror.inverse block2755 ++ GateMirror.inverse block2742 := by rfl
private theorem bPart8 : Partial.leave255InvPart8 = GateMirror.inverse block2715 ++ GateMirror.inverse block2688 ++ GateMirror.inverse block2675 ++ GateMirror.inverse block2646 := by rfl
private theorem bPart9 : Partial.leave255InvPart9 = GateMirror.inverse block2635 ++ GateMirror.inverse block2595 ++ GateMirror.inverse block2592 ++ GateMirror.inverse block2555 ++ GateMirror.inverse block2550 := by rfl
private theorem bPart10 : Partial.leave255InvPart10 = GateMirror.inverse block2515 ++ GateMirror.inverse block2496 ++ GateMirror.inverse block2480 ++ GateMirror.inverse block2454 := by rfl
private theorem bPart11 : Partial.leave255InvPart11 = GateMirror.inverse block2440 ++ GateMirror.inverse block2400 ++ GateMirror.inverse block2360 ++ GateMirror.inverse block2358 := by rfl
private theorem bPart12 : Partial.leave255InvPart12 = GateMirror.inverse block2320 ++ GateMirror.inverse block2304 ++ GateMirror.inverse block2280 ++ GateMirror.inverse block2262 := by rfl
private theorem bPart13 : Partial.leave255InvPart13 = GateMirror.inverse block2240 ++ GateMirror.inverse block2208 ++ GateMirror.inverse block2200 ++ GateMirror.inverse block2166 := by rfl
private theorem bPart14 : Partial.leave255InvPart14 = GateMirror.inverse block2160 ++ GateMirror.inverse block2120 ++ GateMirror.inverse block2112 ++ GateMirror.inverse block2080 ++ GateMirror.inverse block2070 := by rfl
private theorem bPart15 : Partial.leave255InvPart15 = GateMirror.inverse block2040 ++ GateMirror.inverse block2016 ++ GateMirror.inverse block2000 ++ GateMirror.inverse block1974 := by rfl
private theorem bPart16 : Partial.leave255InvPart16 = GateMirror.inverse block1960 ++ GateMirror.inverse block1920 ++ GateMirror.inverse block1880 ++ GateMirror.inverse block1878 := by rfl
private theorem bPart17 : Partial.leave255InvPart17 = GateMirror.inverse block1840 ++ GateMirror.inverse block1824 ++ GateMirror.inverse block1800 ++ GateMirror.inverse block1782 := by rfl
private theorem bPart18 : Partial.leave255InvPart18 = GateMirror.inverse block1760 ++ GateMirror.inverse block1728 ++ GateMirror.inverse block1720 ++ GateMirror.inverse block1686 := by rfl
private theorem bPart19 : Partial.leave255InvPart19 = GateMirror.inverse block1680 ++ GateMirror.inverse block1640 ++ GateMirror.inverse block1632 ++ GateMirror.inverse block1600 ++ GateMirror.inverse block1590 := by rfl
private theorem bPart20 : Partial.leave255InvPart20 = GateMirror.inverse block1560 ++ GateMirror.inverse block1536 ++ GateMirror.inverse block1520 ++ GateMirror.inverse block1494 := by rfl
private theorem bPart21 : Partial.leave255InvPart21 = GateMirror.inverse block1480 ++ GateMirror.inverse block1440 ++ GateMirror.inverse block1400 ++ GateMirror.inverse block1398 := by rfl
private theorem bPart22 : Partial.leave255InvPart22 = GateMirror.inverse block1360 ++ GateMirror.inverse block1344 ++ GateMirror.inverse block1320 ++ GateMirror.inverse block1302 := by rfl
private theorem bPart23 : Partial.leave255InvPart23 = GateMirror.inverse block1280 ++ GateMirror.inverse block1248 ++ GateMirror.inverse block1240 ++ GateMirror.inverse block1206 := by rfl
private theorem bPart24 : Partial.leave255InvPart24 = GateMirror.inverse block1200 ++ GateMirror.inverse block1160 ++ GateMirror.inverse block1152 ++ GateMirror.inverse block1120 ++ GateMirror.inverse block1110 := by rfl
private theorem bPart25 : Partial.leave255InvPart25 = GateMirror.inverse block1080 ++ GateMirror.inverse block1056 ++ GateMirror.inverse block1040 ++ GateMirror.inverse block1014 := by rfl
private theorem bPart26 : Partial.leave255InvPart26 = GateMirror.inverse block1000 ++ GateMirror.inverse block960 ++ GateMirror.inverse block920 ++ GateMirror.inverse block918 := by rfl
private theorem bPart27 : Partial.leave255InvPart27 = GateMirror.inverse block880 ++ GateMirror.inverse block864 ++ GateMirror.inverse block840 ++ GateMirror.inverse block822 := by rfl
private theorem bPart28 : Partial.leave255InvPart28 = GateMirror.inverse block800 ++ GateMirror.inverse block768 ++ GateMirror.inverse block760 ++ GateMirror.inverse block726 := by rfl
private theorem bPart29 : Partial.leave255InvPart29 = GateMirror.inverse block720 ++ GateMirror.inverse block680 ++ GateMirror.inverse block672 ++ GateMirror.inverse block640 ++ GateMirror.inverse block630 := by rfl
private theorem bPart30 : Partial.leave255InvPart30 = GateMirror.inverse block600 ++ GateMirror.inverse block576 ++ GateMirror.inverse block560 ++ GateMirror.inverse block534 := by rfl
private theorem bPart31 : Partial.leave255InvPart31 = GateMirror.inverse block520 ++ GateMirror.inverse block480 ++ GateMirror.inverse block440 ++ GateMirror.inverse block438 := by rfl
private theorem bPart32 : Partial.leave255InvPart32 = GateMirror.inverse block400 ++ GateMirror.inverse block384 ++ GateMirror.inverse block360 ++ GateMirror.inverse block342 := by rfl
private theorem bPart33 : Partial.leave255InvPart33 = GateMirror.inverse block320 ++ GateMirror.inverse block288 ++ GateMirror.inverse block280 ++ GateMirror.inverse block246 := by rfl
private theorem bPart34 : Partial.leave255InvPart34 = GateMirror.inverse block240 ++ GateMirror.inverse block200 ++ GateMirror.inverse block192 ++ GateMirror.inverse block160 ++ GateMirror.inverse block150 := by rfl
private theorem bPart35 : Partial.leave255InvPart35 = GateMirror.inverse block120 ++ GateMirror.inverse block96 ++ GateMirror.inverse block80 ++ GateMirror.inverse block54 := by rfl
private theorem bPart36 : Partial.leave255InvPart36 = GateMirror.inverse block40 ++ GateMirror.inverse block0 := by rfl
private theorem bEq : GateMirror.inverse ops = Partial.leave255Inv := by
  simp only [ops,group0,group1,group2,suffix0,suffix40,suffix54,suffix80,suffix96,suffix120,suffix150,suffix160,suffix192,suffix200,suffix240,suffix246,suffix280,suffix288,suffix320,suffix342,suffix360,suffix384,suffix400,suffix438,suffix440,suffix480,suffix520,suffix534,suffix560,suffix576,suffix600,suffix630,suffix640,suffix672,suffix680,suffix720,suffix726,suffix760,suffix768,suffix800,suffix822,suffix840,suffix864,suffix880,suffix918,suffix920,suffix960,suffix1000,suffix1014,suffix1040,suffix1056,suffix1080,suffix1110,suffix1120,suffix1152,suffix1160,suffix1200,suffix1206,suffix1240,suffix1248,suffix1280,suffix1302,suffix1320,suffix1344,suffix1360,suffix1398,suffix1400,suffix1440,suffix1480,suffix1494,suffix1520,suffix1536,suffix1560,suffix1590,suffix1600,suffix1632,suffix1640,suffix1680,suffix1686,suffix1720,suffix1728,suffix1760,suffix1782,suffix1800,suffix1824,suffix1840,suffix1878,suffix1880,suffix1920,suffix1960,suffix1974,suffix2000,suffix2016,suffix2040,suffix2070,suffix2080,suffix2112,suffix2120,suffix2160,suffix2166,suffix2200,suffix2208,suffix2240,suffix2262,suffix2280,suffix2304,suffix2320,suffix2358,suffix2360,suffix2400,suffix2440,suffix2454,suffix2480,suffix2496,suffix2515,suffix2550,suffix2555,suffix2592,suffix2595,suffix2635,suffix2646,suffix2675,suffix2688,suffix2715,suffix2742,suffix2755,suffix2784,suffix2795,suffix2835,suffix2838,suffix2875,suffix2880,suffix2915,suffix2934,suffix2955,suffix2976,suffix2995,suffix3030,suffix3035,suffix3072,suffix3075,suffix3115,suffix3126,suffix3155,suffix3162,suffix3168,suffix3202,suffix3222,suffix3242,suffix3264,suffix3282,suffix3318,suffix3322,suffix3360,suffix3362,suffix3402,suffix3414,suffix3442,suffix3456,suffix3482,bwAppend,List.append_nil,Partial.leave255Inv,bPart0,bPart1,bPart2,bPart3,bPart4,bPart5,bPart6,bPart7,bPart8,bPart9,bPart10,bPart11,bPart12,bPart13,bPart14,bPart15,bPart16,bPart17,bPart18,bPart19,bPart20,bPart21,bPart22,bPart23,bPart24,bPart25,bPart26,bPart27,bPart28,bPart29,bPart30,bPart31,bPart32,bPart33,bPart34,bPart35,bPart36,List.append_assoc]
private theorem len0 : block0.length=40:=rfl
private theorem len40 : block40.length=14:=rfl
private theorem len54 : block54.length=26:=rfl
private theorem len80 : block80.length=16:=rfl
private theorem len96 : block96.length=24:=rfl
private theorem len120 : block120.length=30:=rfl
private theorem len150 : block150.length=10:=rfl
private theorem len160 : block160.length=32:=rfl
private theorem len192 : block192.length=8:=rfl
private theorem len200 : block200.length=40:=rfl
private theorem len240 : block240.length=6:=rfl
private theorem len246 : block246.length=34:=rfl
private theorem len280 : block280.length=8:=rfl
private theorem len288 : block288.length=32:=rfl
private theorem len320 : block320.length=22:=rfl
private theorem len342 : block342.length=18:=rfl
private theorem len360 : block360.length=24:=rfl
private theorem len384 : block384.length=16:=rfl
private theorem len400 : block400.length=38:=rfl
private theorem len438 : block438.length=2:=rfl
private theorem len440 : block440.length=40:=rfl
private theorem len480 : block480.length=40:=rfl
private theorem len520 : block520.length=14:=rfl
private theorem len534 : block534.length=26:=rfl
private theorem len560 : block560.length=16:=rfl
private theorem len576 : block576.length=24:=rfl
private theorem len600 : block600.length=30:=rfl
private theorem len630 : block630.length=10:=rfl
private theorem len640 : block640.length=32:=rfl
private theorem len672 : block672.length=8:=rfl
private theorem len680 : block680.length=40:=rfl
private theorem len720 : block720.length=6:=rfl
private theorem len726 : block726.length=34:=rfl
private theorem len760 : block760.length=8:=rfl
private theorem len768 : block768.length=32:=rfl
private theorem len800 : block800.length=22:=rfl
private theorem len822 : block822.length=18:=rfl
private theorem len840 : block840.length=24:=rfl
private theorem len864 : block864.length=16:=rfl
private theorem len880 : block880.length=38:=rfl
private theorem len918 : block918.length=2:=rfl
private theorem len920 : block920.length=40:=rfl
private theorem len960 : block960.length=40:=rfl
private theorem len1000 : block1000.length=14:=rfl
private theorem len1014 : block1014.length=26:=rfl
private theorem len1040 : block1040.length=16:=rfl
private theorem len1056 : block1056.length=24:=rfl
private theorem len1080 : block1080.length=30:=rfl
private theorem len1110 : block1110.length=10:=rfl
private theorem len1120 : block1120.length=32:=rfl
private theorem len1152 : block1152.length=8:=rfl
private theorem len1160 : block1160.length=40:=rfl
private theorem len1200 : block1200.length=6:=rfl
private theorem len1206 : block1206.length=34:=rfl
private theorem len1240 : block1240.length=8:=rfl
private theorem len1248 : block1248.length=32:=rfl
private theorem len1280 : block1280.length=22:=rfl
private theorem len1302 : block1302.length=18:=rfl
private theorem len1320 : block1320.length=24:=rfl
private theorem len1344 : block1344.length=16:=rfl
private theorem len1360 : block1360.length=38:=rfl
private theorem len1398 : block1398.length=2:=rfl
private theorem len1400 : block1400.length=40:=rfl
private theorem len1440 : block1440.length=40:=rfl
private theorem len1480 : block1480.length=14:=rfl
private theorem len1494 : block1494.length=26:=rfl
private theorem len1520 : block1520.length=16:=rfl
private theorem len1536 : block1536.length=24:=rfl
private theorem len1560 : block1560.length=30:=rfl
private theorem len1590 : block1590.length=10:=rfl
private theorem len1600 : block1600.length=32:=rfl
private theorem len1632 : block1632.length=8:=rfl
private theorem len1640 : block1640.length=40:=rfl
private theorem len1680 : block1680.length=6:=rfl
private theorem len1686 : block1686.length=34:=rfl
private theorem len1720 : block1720.length=8:=rfl
private theorem len1728 : block1728.length=32:=rfl
private theorem len1760 : block1760.length=22:=rfl
private theorem len1782 : block1782.length=18:=rfl
private theorem len1800 : block1800.length=24:=rfl
private theorem len1824 : block1824.length=16:=rfl
private theorem len1840 : block1840.length=38:=rfl
private theorem len1878 : block1878.length=2:=rfl
private theorem len1880 : block1880.length=40:=rfl
private theorem len1920 : block1920.length=40:=rfl
private theorem len1960 : block1960.length=14:=rfl
private theorem len1974 : block1974.length=26:=rfl
private theorem len2000 : block2000.length=16:=rfl
private theorem len2016 : block2016.length=24:=rfl
private theorem len2040 : block2040.length=30:=rfl
private theorem len2070 : block2070.length=10:=rfl
private theorem len2080 : block2080.length=32:=rfl
private theorem len2112 : block2112.length=8:=rfl
private theorem len2120 : block2120.length=40:=rfl
private theorem len2160 : block2160.length=6:=rfl
private theorem len2166 : block2166.length=34:=rfl
private theorem len2200 : block2200.length=8:=rfl
private theorem len2208 : block2208.length=32:=rfl
private theorem len2240 : block2240.length=22:=rfl
private theorem len2262 : block2262.length=18:=rfl
private theorem len2280 : block2280.length=24:=rfl
private theorem len2304 : block2304.length=16:=rfl
private theorem len2320 : block2320.length=38:=rfl
private theorem len2358 : block2358.length=2:=rfl
private theorem len2360 : block2360.length=40:=rfl
private theorem len2400 : block2400.length=40:=rfl
private theorem len2440 : block2440.length=14:=rfl
private theorem len2454 : block2454.length=26:=rfl
private theorem len2480 : block2480.length=16:=rfl
private theorem len2496 : block2496.length=19:=rfl
private theorem size0 : (GateMirror.forward group0).length=2515:=by
  simp only [GateMirror.forward,List.length_map,group0,suffix0,suffix40,suffix54,suffix80,suffix96,suffix120,suffix150,suffix160,suffix192,suffix200,suffix240,suffix246,suffix280,suffix288,suffix320,suffix342,suffix360,suffix384,suffix400,suffix438,suffix440,suffix480,suffix520,suffix534,suffix560,suffix576,suffix600,suffix630,suffix640,suffix672,suffix680,suffix720,suffix726,suffix760,suffix768,suffix800,suffix822,suffix840,suffix864,suffix880,suffix918,suffix920,suffix960,suffix1000,suffix1014,suffix1040,suffix1056,suffix1080,suffix1110,suffix1120,suffix1152,suffix1160,suffix1200,suffix1206,suffix1240,suffix1248,suffix1280,suffix1302,suffix1320,suffix1344,suffix1360,suffix1398,suffix1400,suffix1440,suffix1480,suffix1494,suffix1520,suffix1536,suffix1560,suffix1590,suffix1600,suffix1632,suffix1640,suffix1680,suffix1686,suffix1720,suffix1728,suffix1760,suffix1782,suffix1800,suffix1824,suffix1840,suffix1878,suffix1880,suffix1920,suffix1960,suffix1974,suffix2000,suffix2016,suffix2040,suffix2070,suffix2080,suffix2112,suffix2120,suffix2160,suffix2166,suffix2200,suffix2208,suffix2240,suffix2262,suffix2280,suffix2304,suffix2320,suffix2358,suffix2360,suffix2400,suffix2440,suffix2454,suffix2480,suffix2496,len0,len40,len54,len80,len96,len120,len150,len160,len192,len200,len240,len246,len280,len288,len320,len342,len360,len384,len400,len438,len440,len480,len520,len534,len560,len576,len600,len630,len640,len672,len680,len720,len726,len760,len768,len800,len822,len840,len864,len880,len918,len920,len960,len1000,len1014,len1040,len1056,len1080,len1110,len1120,len1152,len1160,len1200,len1206,len1240,len1248,len1280,len1302,len1320,len1344,len1360,len1398,len1400,len1440,len1480,len1494,len1520,len1536,len1560,len1590,len1600,len1632,len1640,len1680,len1686,len1720,len1728,len1760,len1782,len1800,len1824,len1840,len1878,len1880,len1920,len1960,len1974,len2000,len2016,len2040,len2070,len2080,len2112,len2120,len2160,len2166,len2200,len2208,len2240,len2262,len2280,len2304,len2320,len2358,len2360,len2400,len2440,len2454,len2480,len2496,List.length_append,List.length_nil]
private theorem len2515 : block2515.length=35:=rfl
private theorem len2550 : block2550.length=5:=rfl
private theorem len2555 : block2555.length=37:=rfl
private theorem len2592 : block2592.length=3:=rfl
private theorem len2595 : block2595.length=40:=rfl
private theorem len2635 : block2635.length=11:=rfl
private theorem len2646 : block2646.length=29:=rfl
private theorem len2675 : block2675.length=13:=rfl
private theorem len2688 : block2688.length=27:=rfl
private theorem len2715 : block2715.length=27:=rfl
private theorem len2742 : block2742.length=13:=rfl
private theorem len2755 : block2755.length=29:=rfl
private theorem len2784 : block2784.length=11:=rfl
private theorem len2795 : block2795.length=40:=rfl
private theorem len2835 : block2835.length=3:=rfl
private theorem len2838 : block2838.length=37:=rfl
private theorem len2875 : block2875.length=5:=rfl
private theorem len2880 : block2880.length=35:=rfl
private theorem len2915 : block2915.length=19:=rfl
private theorem len2934 : block2934.length=21:=rfl
private theorem len2955 : block2955.length=21:=rfl
private theorem len2976 : block2976.length=19:=rfl
private theorem len2995 : block2995.length=35:=rfl
private theorem len3030 : block3030.length=5:=rfl
private theorem len3035 : block3035.length=37:=rfl
private theorem len3072 : block3072.length=3:=rfl
private theorem len3075 : block3075.length=40:=rfl
private theorem len3115 : block3115.length=11:=rfl
private theorem len3126 : block3126.length=29:=rfl
private theorem len3155 : block3155.length=7:=rfl
private theorem size1 : (GateMirror.forward group1).length=647:=by
  simp only [GateMirror.forward,List.length_map,group1,suffix2515,suffix2550,suffix2555,suffix2592,suffix2595,suffix2635,suffix2646,suffix2675,suffix2688,suffix2715,suffix2742,suffix2755,suffix2784,suffix2795,suffix2835,suffix2838,suffix2875,suffix2880,suffix2915,suffix2934,suffix2955,suffix2976,suffix2995,suffix3030,suffix3035,suffix3072,suffix3075,suffix3115,suffix3126,suffix3155,len2515,len2550,len2555,len2592,len2595,len2635,len2646,len2675,len2688,len2715,len2742,len2755,len2784,len2795,len2835,len2838,len2875,len2880,len2915,len2934,len2955,len2976,len2995,len3030,len3035,len3072,len3075,len3115,len3126,len3155,List.length_append,List.length_nil]
private theorem pEq : GateMirror.forward group0 = Partial.leave255.take 2515 := by
  rw [←fEq,ops,fwAppend,←size0,List.take_left]
private theorem qEq : GateMirror.forward (group0++group1) = Partial.leave255.take 3162 := by
  have lengthEq:(GateMirror.forward (group0++group1)).length=3162:=by rw [fwAppend,List.length_append,size0,size1]
  rw [←fEq,ops,←List.append_assoc,fwAppend (group0++group1) group2,←lengthEq,List.take_left]
theorem inverts (s:State) (phase:∀m,(run Partial.leave255 m s).phase=s.phase)
    (initial:∀q, 1556≤q → q≤1702 → s.basis q=false)
    (extra:∀q, 1713≤q → q≤1718 → s.basis q=false)
    (core:zeros (run (Partial.leave255.take 2515) [] s) [1560,1576,1596,1613,1614])
    (post:(run (Partial.leave255.take 3162) [] s).basis 1556=false) (m n:List Bool):
    run Partial.leave255Inv n (run Partial.leave255 m s)=s:=by
  let s1:=run (GateMirror.forward group0) [] s
  let s2:=run (GateMirror.forward group1) [] s1
  have s2e:s2=run (GateMirror.forward (group0++group1)) [] s:=by
    simp [s2,s1,GateMirror.forward,List.map_append,run_append]
  have i0:Masked s (0x7e007fffffffffffffffffffffffffeffffeffffe <<< 1556):=subMask (by decide +kernel) (bothMasks (fromRange (lo:=1556) (width:=147) (fun q h1 h2=>initial q h1 (Nat.le_of_lt_succ h2))) (fromRange (lo:=1713) (width:=6) (fun q h1 h2=>extra q h1 (Nat.le_of_lt_succ h2))))
  obtain ⟨h0,r0,z0⟩:=bit_sound group0 s _ _ cert0 i0
  have kc:zeros s1 [1560,1576,1596,1613,1614]:=by simpa only [s1,pEq] using core
  have i1:Masked s1 (0xfffffffffffffffffffe0003fffffffff8 <<< 1556):=subMask (by decide +kernel) (bothMasks z0 (fromList kc))
  obtain ⟨h1,r1,z1⟩:=bit_sound group1 s1 _ _ cert1 i1
  have kp:zeros s2 [1556]:=by
    intro q hq
    obtain rfl: q=1556:=by simpa using hq
    rw [s2e,qEq];exact post
  have i2:Masked s2 (0x79 <<< 1556):=subMask (by decide +kernel) (bothMasks z1 (fromList kp))
  obtain ⟨h2,r2,z2⟩:=bit_sound group2 s2 _ _ cert2 i2
  have phys:∀g∈ops,proper g=true:=by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact h0 g h
    · rcases List.mem_append.mp h with h|h
      · exact h1 g h
      · exact h2 g h
  have ready:Ready s ops:=ready_append _ _ _ r0 (ready_append _ _ _ r1 r2)
  rw [←bEq,←fEq]
  exact invert ops s phys (all_prepared ops s phys (by rwa [fEq])) ready m n
end ECDSAAdd.Entrant.StairPacket.Leave255Mirror


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Join Leave225Word

def program:=leave225.take 2260
theorem shape:program=entry++Leave225Routed.body := by decide +kernel
def rawSites:=List.range' 1613 105 ++ List.range' 1726 87
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 112,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  have front:=Leave225Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave225FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 112,97 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave225Hit.swaps i):=by decide +kernel
  have used:=Leave225Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave225EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave225EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave225Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Join Leave240Word

def program:=leave240.take 2395
theorem shape:program=entry++Leave240Routed.body := by decide +kernel
def rawSites:=List.range' 1613 97 ++ List.range' 1718 95
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 120,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  have front:=Leave240Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave240FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 120,105 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave240Hit.swaps i):=by decide +kernel
  have used:=Leave240Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave240EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave240EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave240Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Join Leave255Word

def program:=leave255.take 2515
theorem shape:program=entry++Leave255Routed.body := by decide +kernel
def rawSites:=List.range' 1613 90 ++ List.range' 1711 89
def magSites:=fullM
def targets:List Wire:=List.range' 1559 39 ++ (List.finRange 18).map (fun j=>(row j).free) ++ rawSites ++ magSites

theorem geometry:∀q∈rawSites++magSites,(∀i:Fin 127,q≠wire i.val) ∧ (∀r∈columns,q≠r.shadow ∧ q≠r.tube) ∧
    q∉(fullPrefix false).map destination ∧ ¬(1559≤q ∧ q≤1597) := by decide +kernel
theorem rawSafe:∀q∈rawSites,q∉entry.map destination := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z))) :
    let out:=run program m s
    (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧
    (∀q∈rawSites,out.basis q=s.basis q) ∧ (∀q∈magSites,out.basis q=false) := by
  let a:=run entry m s
  let n:=m.drop (measurementCount entry)
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  have front:=Leave255Front.result s m z G sg small ready fresh scratch temp
  have watched:=Leave255FrontReady.frame s m z G sg small ready fresh scratch temp
  have kept (q:Wire) (ok:unmodified q):a.basis q=s.basis q:=preserved entry s m q ok
  have cs:∀q∈carries,unmodified q:=by decide +kernel
  have pad:∀i:Fin 127,112 ≤ i.val → unmodified (wire i):=by decide +kernel
  have rawBank:∀q∈ys,unmodified q:=by decide +kernel
  have sw:∀i:Fin 15,unmodified (Leave255Hit.swaps i):=by decide +kernel
  have used:=Leave255Routed.result z a n small odd room (fun q hq=>(kept _ (cs q hq)).trans (clean q hq))
    (fun i lo hi=>(kept _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (Leave255EntryAction.upperBits h a.basis front.2.2.2.2.2)
    (((regValue_eq_iff _ _ _).mpr (fun q hq=>kept _ (rawBank _ hq))).trans bank)
    (fun q hq=>(watched _ hq).trans (zero _ hq))
    ((Leave255EntryAction.parity s m).trans par)
    (by rw [kept _ (by decide),kept _ (by decide)];exact mode)
    (fun on i hi hq=>(kept _ (sw ⟨i,hi⟩)).trans (events on i hi hq))
  have other (q:Wire) (mem:q∈rawSites++magSites) : (run Leave255Routed.body n a).basis q=a.basis q := by
    obtain ⟨away,cols,sel,mask⟩:=geometry q mem
    rw [used.2.2.2.2 q (fun i hi=>away ⟨i,hi⟩) cols,cleared,if_neg mask]
    exact preserved _ a n q sel
  dsimp only
  rw [shape,run_append,run_take]
  refine ⟨used.2.2.2.1,used.2.2.1,?_,?_⟩
  · intro q h
    exact (other _ (List.mem_append_left _ h)).trans (kept _ (rawSafe _ h))
  · intro q h
    have set:∀q∈magSites,q∈fullM:=by decide +kernel
    exact (other _ (List.mem_append_right _ h)).trans ((regValue_zero _ _).mp front.2.1 q (set _ h))

theorem oracle (s out:State) (scr:∀j:Fin 39,out.basis (1559+j.val)=false)
    (raw:∀q∈rawSites,out.basis q=s.basis q) (clean:∀q∈carries,s.basis q=false) :
    ∀q∈[1560,1576,1596,1613,1614],out.basis q=false := by
  have cases:∀q∈[1560,1576,1596,1613,1614],(∃j:Fin 39,q=1559+j.val) ∨ (q∈rawSites ∧ q∈carries) := by decide +kernel
  intro q mem
  rcases cases q mem with ⟨j,rfl⟩|⟨a,b⟩
  · exact scr j
  · exact (raw q a).trans (clean q b)

end ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112)
    (phase:∀o,(run leave225 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1717→s.basis q=false)
    : run leave225Inv n (run leave225 m s)=s:=by
  have atCore:=Leave225CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave225PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave225Mirror.inverts s phase initial  _ _ m n
  · exact Leave225CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1269,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120)
    (phase:∀o,(run leave240 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1709→s.basis q=false)
    : run leave240Inv n (run leave240 m s)=s:=by
  have atCore:=Leave240CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave240PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave240Mirror.inverts s phase initial  _ _ m n
  · exact Leave240CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1284,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
attribute [local irreducible] run SkywalkNat.step
theorem result (s : State) (m n : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127)
    (phase:∀o,(run leave255 o s).phase=s.phase)
    (initial:∀q,1556≤q→q≤1702→s.basis q=false)
    (extra:∀q,1713≤q→q≤1718→s.basis q=false)
    : run leave255Inv n (run leave255 m s)=s:=by
  have atCore:=Leave255CoreCheckpoint.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have atPost:=Leave255PostReady.result s [] z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events nextSmall bound
  apply Leave255Mirror.inverts s phase initial extra  _ _ m n
  · exact Leave255CoreCheckpoint.oracle s _ atCore.1 atCore.2.2.1 clean
  · exact (atPost.2.2.2.2 (1299,1556) (by decide)).2
end ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip


end
