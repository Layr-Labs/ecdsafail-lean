import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeTail227303371

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveNoSwap
open Arithmetic PortalAnd

def block (a out:Wire) : List (Wire×Wire) → Program
  | [] => [.CX a out]
  | (x,t)::ps => [.X x,.CCX a x t] ++ block t out ps ++ [.measureX t [] [.CZ a x],.X x]

theorem action (ps:List (Wire×Wire)) (a out:Wire) (s:State) (m:List Bool)
    (nd:(out::a::sites ps).Nodup) (cold:∀p∈ps,s.basis p.2=false) :
    run (block a out ps) m s=⟨s.phase,writeBit s.basis out (s.basis out ^^ (s.basis a && ps.all (fun p=> !s.basis p.1)))⟩ := by
  induction ps generalizing a s m with
  | nil => simp [block,run]
  | cons pr ps ih =>
    obtain ⟨x,t⟩:=pr
    change (out::a::x::t::sites ps).Nodup at nd
    obtain ⟨oa,ox,ot,os,ax,at',as',xt,xs,ts,ns⟩ :
      out≠a ∧ out≠x ∧ out≠t ∧ out∉sites ps ∧ a≠x ∧ a≠t ∧ a∉sites ps ∧
        x≠t ∧ x∉sites ps ∧ t∉sites ps ∧ (sites ps).Nodup := by simpa [and_assoc] using nd
    let v:State:=⟨s.phase,writeBit (writeBit s.basis x (!s.basis x)) t (s.basis a && !s.basis x)⟩
    have z:=cold (x,t) (by simp)
    change s.basis t=false at z
    have enter : run [.X x,.CCX a x t] m s=v := by simp [run,v,writeBit,Function.update,ax,xt.symm,z]
    have keep (q:Wire) (hx:q≠x) (ht:q≠t) : v.basis q=s.basis q := by simp [v,writeBit,hx,ht]
    have same (p:Wire×Wire) (hp:p∈ps) : v.basis p.1=s.basis p.1 ∧ v.basis p.2=s.basis p.2 := by
      have l:p.1∈sites ps:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
      have r:p.2∈sites ps:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
      exact ⟨keep _ (fun h=>xs (h ▸ l)) (fun h=>ts (h ▸ l)),keep _ (fun h=>xs (h ▸ r)) (fun h=>ts (h ▸ r))⟩
    have bits : ps.all (fun p=> !v.basis p.1)=ps.all (fun p=> !s.basis p.1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro H p hp
      · simpa only [(same p hp).1] using H p hp
      · rw [(same p hp).1];exact H p hp
    have act:=ih t v m (by simp [ot,os,ts,ns]) (fun p hp=>(same p hp).2.trans (cold p (by simp [hp])))
    simp only [block,run_append,run_take]
    rw [enter]
    change run [.measureX t [] [.CZ a x],.X x] _ (run (block t out ps) m v)=_
    rw [act,bits,keep out ox ot]
    have vt:v.basis t=(s.basis a && !s.basis x) := by simp [v,writeBit]
    rw [vt]
    simp only [List.all_cons,Bool.and_assoc]
    generalize (s.basis out ^^ (s.basis a && (!s.basis x && ps.all (fun p=> !s.basis p.1))))=ans
    let w:State:=⟨v.phase,writeBit v.basis out ans⟩
    have cleanup:w.basis t=(w.basis a && w.basis x) := by
      simp [w,v,writeBit,Function.update,ot.symm,oa.symm,ox.symm,at',ax,xt]
    change run ([.measureX t [] [.CZ a x]]++[.X x]) _ w=_
    rw [run_append,run_take,measure_and _ _ _ _ _ at' xt cleanup]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=x <;> by_cases ht:q=t <;> by_cases ho:q=out <;> simp_all [run,w,v,writeBit,Function.update]

end ECDSAAdd.Entrant.StairPacket.LeaveNoSwap


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Close
open Arithmetic Partial RailPair Leave225Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def history : List Wire := [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
def low : List (Wire×Wire) := [(400, 930), (401, 931), (402, 932), (403, 933), (404, 934), (405, 935), (406, 936), (407, 937), (408, 938), (409, 939), (410, 940)]
def events : List (Wire×Wire) := [(1269, 1556), (1270, 1559), (1271, 1560), (1272, 1561), (1273, 1562)]
def beforeTags := (leave225.drop 2788).take 59
def afterLow := leave225.drop 2847
def ending := leave225.drop 2788

theorem lowShape : beforeTags=notRegister history++store 255 1723 low [] := by decide +kernel
theorem tailShape : afterLow=LeaveNoSwap.block 1725 1722 events++lastPart := by decide +kernel
theorem split : ending=beforeTags++afterLow := by decide +kernel

theorem lowResult (s:State) (m:List Bool) :
    let h:=fun q=>if q∈history then !s.basis q else s.basis q
    let t:=run beforeTags m s
    t.phase=s.phase ∧ (∀q,q∉sites low → t.basis q=h q) ∧
      ∀p∈low,t.basis p.1=(if h 255 then h p.2 ^^ h 1723 else h p.1) ∧
        t.basis p.2=(if h 255 then h p.1 else h p.2 ^^ h 1723) := by
  dsimp only
  rw [lowShape,run_append,run_take,notRegister_correct _ (by decide)]
  let h:State:=⟨s.phase,fun q=>if q∈history then !s.basis q else s.basis q⟩
  have geom : StoreGeometry 255 1723 low [] := by constructor <;> decide +kernel
  have act:=store_run 255 1723 low [] geom h (m.drop (measurementCount (notRegister history))) (by simp)
  exact ⟨act.1,fun q no=>act.2.1 q no (by simp [sites]),act.2.2.2⟩

theorem after (s:State) (m:List Bool) (cold:∀p∈events,s.basis p.2=false) :
    let toggled:=s.basis 1722 ^^ (s.basis 1725 && events.all (fun p=> !s.basis p.1))
    run afterLow m s=⟨s.phase,fun q=>(writeBit s.basis 1722 toggled) (LeaveRelocation.source moves q)⟩ := by
  rw [tailShape,run_append,run_take,LeaveNoSwap.action _ _ _ _ _ (by decide +kernel) cold,Leave225Relocated.forward]

end ECDSAAdd.Entrant.StairPacket.Leave225Close


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Close
open Arithmetic Partial RailPair Leave240Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def history : List Wire := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270]
def low : List (Wire×Wire) := [(407, 922), (408, 923), (409, 924), (410, 925), (411, 926), (412, 927), (413, 928), (414, 929), (415, 930), (416, 931), (417, 932), (418, 933)]
def events : List (Wire×Wire) := [(1284, 1556), (1285, 1559), (1286, 1560), (1287, 1561), (1288, 1562)]
def beforeTags := (leave240.drop 2961).take 63
def afterLow := leave240.drop 3024
def ending := leave240.drop 2961

theorem lowShape : beforeTags=notRegister history++store 270 1715 low [] := by decide +kernel
theorem tailShape : afterLow=LeaveNoSwap.block 1717 1714 events++lastPart := by decide +kernel
theorem split : ending=beforeTags++afterLow := by decide +kernel

theorem lowResult (s:State) (m:List Bool) :
    let h:=fun q=>if q∈history then !s.basis q else s.basis q
    let t:=run beforeTags m s
    t.phase=s.phase ∧ (∀q,q∉sites low → t.basis q=h q) ∧
      ∀p∈low,t.basis p.1=(if h 270 then h p.2 ^^ h 1715 else h p.1) ∧
        t.basis p.2=(if h 270 then h p.1 else h p.2 ^^ h 1715) := by
  dsimp only
  rw [lowShape,run_append,run_take,notRegister_correct _ (by decide)]
  let h:State:=⟨s.phase,fun q=>if q∈history then !s.basis q else s.basis q⟩
  have geom : StoreGeometry 270 1715 low [] := by constructor <;> decide +kernel
  have act:=store_run 270 1715 low [] geom h (m.drop (measurementCount (notRegister history))) (by simp)
  exact ⟨act.1,fun q no=>act.2.1 q no (by simp [sites]),act.2.2.2⟩

theorem after (s:State) (m:List Bool) (cold:∀p∈events,s.basis p.2=false) :
    let toggled:=s.basis 1714 ^^ (s.basis 1717 && events.all (fun p=> !s.basis p.1))
    run afterLow m s=⟨s.phase,fun q=>(writeBit s.basis 1714 toggled) (LeaveRelocation.source moves q)⟩ := by
  rw [tailShape,run_append,run_take,LeaveNoSwap.action _ _ _ _ _ (by decide +kernel) cold,Leave240Relocated.forward]

end ECDSAAdd.Entrant.StairPacket.Leave240Close


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Close
open Arithmetic Partial RailPair Leave255Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def history : List Wire := [271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285]
def low : List (Wire×Wire) := [(415, 915), (416, 916), (417, 917), (418, 918), (419, 919), (420, 920), (421, 921), (422, 922), (423, 923), (424, 924), (425, 925)]
def events : List (Wire×Wire) := [(1299, 1556), (1300, 1559), (1812, 1560), (1811, 1561), (1810, 1562)]
def beforeTags := (leave255.drop 3103).take 59
def afterLow := leave255.drop 3162
def ending := leave255.drop 3103

theorem lowShape : beforeTags=notRegister history++store 285 1708 low [] := by decide +kernel
theorem tailShape : afterLow=LeaveNoSwap.block 1710 1707 events++lastPart := by decide +kernel
theorem split : ending=beforeTags++afterLow := by decide +kernel

theorem lowResult (s:State) (m:List Bool) :
    let h:=fun q=>if q∈history then !s.basis q else s.basis q
    let t:=run beforeTags m s
    t.phase=s.phase ∧ (∀q,q∉sites low → t.basis q=h q) ∧
      ∀p∈low,t.basis p.1=(if h 285 then h p.2 ^^ h 1708 else h p.1) ∧
        t.basis p.2=(if h 285 then h p.1 else h p.2 ^^ h 1708) := by
  dsimp only
  rw [lowShape,run_append,run_take,notRegister_correct _ (by decide)]
  let h:State:=⟨s.phase,fun q=>if q∈history then !s.basis q else s.basis q⟩
  have geom : StoreGeometry 285 1708 low [] := by constructor <;> decide +kernel
  have act:=store_run 285 1708 low [] geom h (m.drop (measurementCount (notRegister history))) (by simp)
  exact ⟨act.1,fun q no=>act.2.1 q no (by simp [sites]),act.2.2.2⟩

theorem after (s:State) (m:List Bool) (cold:∀p∈events,s.basis p.2=false) :
    let toggled:=s.basis 1707 ^^ (s.basis 1710 && events.all (fun p=> !s.basis p.1))
    run afterLow m s=⟨s.phase,fun q=>(writeBit s.basis 1707 toggled) (LeaveRelocation.source moves q)⟩ := by
  rw [tailShape,run_append,run_take,LeaveNoSwap.action _ _ _ _ _ (by decide +kernel) cold,Leave255Relocated.forward]

end ECDSAAdd.Entrant.StairPacket.Leave255Close


end
