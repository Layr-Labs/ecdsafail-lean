import ECDSAAdd.Arithmetic.SignedRecordProgram
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair

theorem PackedCut.unique {lo hi g n f u neg far long origin a b}
    (x:PackedCut lo hi g n f u neg far long origin a) (y:PackedCut lo hi g n f u neg far long origin b) : a=b:=by
  have phase:=x.phase.trans y.phase.symm
  have basis:a.basis=b.basis:=by
    funext q
    by_cases hn:q=n
    · subst q;exact x.sign.trans y.sign.symm
    by_cases hf:q=f
    · subst q;exact x.mode.trans y.mode.symm
    by_cases hu:q=u
    · subst q;exact x.orientation.trans y.orientation.symm
    by_cases hh:q∈sites hi
    · obtain ⟨p,hp,hit⟩:=List.mem_flatMap.mp hh
      rcases List.mem_cons.mp hit with rfl|tail
      · exact (x.upper _ hp).1.trans (y.upper _ hp).1.symm
      · obtain rfl:=List.mem_singleton.mp tail
        exact (x.upper _ hp).2.trans (y.upper _ hp).2.symm
    · exact (x.unchanged _ hn hf hu hh).trans (y.unchanged _ hn hf hu hh).symm
  cases a;cases b;congr
namespace Portal270Flag
set_option exponentiation.threshold 1024
theorem release (z:SkywalkNat.State) (small:min z.u z.v<2^121) (raw packed:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative sg z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u))
      (pullState (OB5.sig 269) raw) packed) :
    run Partial.portal270Inv m packed=pullState (OB5.sig 269) raw := by
  rw [cut.unique (physical_frame_local z small raw [] route sg record)]
  exact portal_return _ [] m (clean_for raw z route sg record)
#print axioms release
end Portal270Flag
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.HighBankSum
open HighBankAdjust

/-- Convert the signed high-bank update into the correction to the saved quotient. -/
theorem corrected (H w d : Nat) (c neg : Bool) (far : 2 ≤ H)
    (room : H-2+d < 2^w) (legal : neg=true → c=true)
    (digit : d=c.toNat+2*(!neg).toNat) : adjusted H w c neg=H-2+d := by
  cases c <;> cases neg <;> simp_all [adjusted,Bool.toNat]
  all_goals first
    | omega
    | exact Nat.mod_eq_of_lt (by omega)
    | rw [Nat.mod_eq_of_lt (by omega)] <;> omega
    | rw [show H+2^w-1 = H-1+2^w by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)] ; omega

/-- The restored word begins at bit E of the actual integer sum. -/
theorem value (F S H w E t : Nat) (c neg : Bool)
    (gap : F=S+2^t*(2^E*(H-2))) (far : 2 ≤ H)
    (room : H-2+S/2^E/2^t < 2^w) (legal : neg=true → c=true)
    (digit : S/2^E/2^t=c.toNat+2*(!neg).toNat) :
    F/2^E = 2^t*adjusted H w c neg + S/2^E%2^t := by
  have h := corrected H w _ c neg far room legal digit
  rw [h,gap,show 2^t*(2^E*(H-2))=2^E*(2^t*(H-2)) by ring,
      Nat.add_mul_div_left _ _ (by positivity),Nat.mul_add]
  have decomposition := Nat.mod_add_div (S/2^E) (2^t)
  omega

end ECDSAAdd.Entrant.StairPacket.HighBankSum

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveRelocation

def one (a b : Wire) : Program := [.CX a b,.CX b a,.CX a b]
def flip (a b q : Wire) := if q=a then b else if q=b then a else q
def program (xs : List (Wire×Wire)) := xs.flatMap (fun p=>one p.1 p.2)
def source (xs : List (Wire×Wire)) (q : Wire) := xs.foldr (fun p i=>flip p.1 p.2 i) q

theorem oneRun (a b : Wire) (diff : a≠b) (s : State) (m : List Bool) :
    run (one a b) m s=⟨s.phase,fun q=>s.basis (flip a b q)⟩ := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases x : q=a <;> by_cases y : q=b <;> simp_all [flip,writeBit,Function.update,Bool.xor_comm,Bool.xor_left_comm]

theorem actual (xs : List (Wire×Wire)) (diff : ∀p∈xs,p.1≠p.2) (s : State) (m : List Bool) :
    run (program xs) m s=⟨s.phase,fun q=>s.basis (source xs q)⟩ := by
  induction xs generalizing s m with
  | nil => rfl
  | cons p rest ih =>
    change run (one p.1 p.2 ++ program rest) m s=_
    rw [run_append,run_take]
    rw [oneRun _ _ (diff p (by simp)),ih (fun t ht=>diff t (List.mem_cons_of_mem _ ht))]
    rfl


theorem outside (xs : List (Wire×Wire)) (q : Wire) (away : ∀p∈xs,q≠p.1 ∧ q≠p.2) : source xs q=q := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change flip p.1 p.2 (source ps q)=q
    rw [ih (fun r h=>away r (List.mem_cons_of_mem _ h))]
    simp [flip,(away p (by simp)).1,(away p (by simp)).2]

theorem append (xs ys : List (Wire×Wire)) (q : Wire) : source (xs++ys) q=source xs (source ys q) := by
  simp [source,List.foldr_append]

theorem undoSources (xs : List (Wire×Wire)) (q : Wire) : source xs (source xs.reverse q)=q := by
  induction xs generalizing q with
  | nil => rfl
  | cons p ps ih =>
    rw [List.reverse_cons,append]
    change flip p.1 p.2 (source ps (source ps.reverse (flip p.1 p.2 q)))=q
    rw [ih]
    by_cases a:q=p.1 <;> by_cases b:q=p.2 <;> simp_all [flip]

end ECDSAAdd.Entrant.StairPacket.LeaveRelocation

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed

def eraseSites (sites:List Wire) (s:State) : State :=
  ⟨s.phase,fun q=>if q∈sites then false else s.basis q⟩

theorem erase_run (sites:List Wire) (P:Program) (avoid:∀q∈sites,q∉wires P) (m:List Bool) (s:State) :
    run P m (eraseSites sites s)=eraseSites sites (run P m s) := by
  have locality:=run_measured_locality P (wires P) (Finset.Subset.refl _) (eraseSites sites s) s m rfl
    (fun q mem=>by simp [eraseSites,show q∉sites from fun hit=>avoid _ hit mem])
  apply congrArg₂ State.mk locality.1
  funext q
  by_cases used:q∈wires P
  · have outside:q∉sites:=fun hit=>avoid _ hit used
    simpa [eraseSites,outside] using locality.2 q used
  · rw [run_preserves_outside _ m (eraseSites sites s) _ used]
    simp only [eraseSites,run_preserves_outside _ m s _ used]

def zeroSites (j:Fin 23) :=
  let p:=shape j
  let L:=ports p 0
  (L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem zero_congr (j:Fin 23) (s t:State) (agree:∀q∈zeroSites j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:onRails j 0 z s.basis) :
    onRails j 0 z t.basis ∧ cell (shape j) 0 (mappedBasis j t.basis)=cell (shape j) 0 (mappedBasis j s.basis) := by
  let p:=shape j
  let L:=ports p 0
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 0 15:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Enter240
def pending : List Wire := [1716,1717,1718]
theorem avoid_enter : ∀q∈pending,q∉wires Partial.enter240 := by decide +kernel
theorem avoid_live : ∀q∈pending,q∉zeroSites idx := by decide +kernel

theorem ready_pending (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^136)
    (cut:PackedCut lowerPairs upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites pending pre))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false)  :
    let t:=run Partial.enter240 m pre
    let T:=Shadow.reduced 136 15 z
    t.phase=pre.phase ∧ onRails idx 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending,t.basis q=pre.basis q := by
  have eq:=erase_run pending Partial.enter240 avoid_enter m pre
  have real:=ready_from_cut raw (eraseSites pending pre) z G S m small cut input hist 
  rw [eq] at real
  refine ⟨real.1,(zero_congr idx _ _ ?_ _ real.2).1,fun q mem=>run_preserves_outside _ m pre _ (avoid_enter _ mem)⟩
  intro q used
  have absent:q∉pending:=fun h=>avoid_live _ h used
  simp [eraseSites,absent]
end Enter240
namespace Enter255
def pending : List Wire := [1709,1710,1711]
theorem avoid_enter : ∀q∈pending,q∉wires Partial.enter255 := by decide +kernel
theorem avoid_live : ∀q∈pending,q∉zeroSites idx := by decide +kernel

theorem ready_pending (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^129)
    (cut:PackedCut lowerPairs upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites pending pre))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run Partial.enter255 m pre
    let T:=Shadow.reduced 129 15 z
    t.phase=pre.phase ∧ onRails idx 0 (SkywalkRails.encode G S T.u T.v) t.basis ∧
      ∀q∈pending,t.basis q=pre.basis q := by
  have eq:=erase_run pending Partial.enter255 avoid_enter m pre
  have real:=ready_from_cut raw (eraseSites pending pre) z G S m small cut input hist endScratch
  rw [eq] at real
  refine ⟨real.1,(zero_congr idx _ _ ?_ _ real.2).1,fun q mem=>run_preserves_outside _ m pre _ (avoid_enter _ mem)⟩
  intro q used
  have absent:q∉pending:=fun h=>avoid_live _ h used
  simp [eraseSites,absent]
end Enter255
#print axioms Enter255.ready_pending
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.HighBankSum
open IntegerHigh SkywalkNat

def total (z : SkywalkNat.State) := z.u+z.v
def cross (d : Nat) := decide (d≠2)

theorem decode (d : Nat) (n : Bool) (h : d=if d=2 then 2 else if n then 1 else 3) :
    d=(cross d).toNat + 2*(!(cross d && n)).toNat := by
  by_cases e : d=2
  · simp [e,cross]
  · rw [if_neg e] at h
    cases n <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> subst d <;> decide

theorem right (k B s H w E : Nat) (hk : 0<k) (ready : guard k s ≤ B)
    (odd : B%2=1) (small : s<2^E) (low : 2*(2^k*2^E)≤B+s) (high : B+s<3*(2^k*2^E))
    (far : 2≤H) :
    let z : SkywalkNat.State := ⟨s,B⟩
    let S := total (step^[k] z)
    let F := total (step^[k] ⟨s,B+2^k*(2^E*(H-2))⟩)
    let t := wait k s
    let d := S/2^E/2^t
    let neg := cross d && negative (oddBits (letters k z))
    H-2+d<2^w →
      d=(cross d).toNat+2*(!neg).toNat ∧ F/2^E=2^t*HighBankAdjust.adjusted H w (cross d) neg+S/2^E%2^t := by
  dsimp only
  intro room
  have q := corrected_digit k B s (2^E) hk ready odd small low high
  dsimp only at q
  rw [Nat.mul_comm (2^_) (2^E),←Nat.div_div_eq_div_mul] at q
  have digit := decode _ _ q
  exact ⟨digit,value _ _ _ _ _ _ _ _ (right_sum k B s _ ready) far room (fun hn => (Bool.and_eq_true_iff.mp hn).1) digit⟩

theorem left (k B s H w E : Nat) (ready : guard k s ≤ B)
    (odd : s%2=1) (small : s<2^E) (low : 2*(2^k*2^E)≤B+s) (high : B+s<3*(2^k*2^E))
    (far : 2≤H) :
    let S := total (step^[k] ⟨B,s⟩)
    let F := total (step^[k] ⟨B+2^k*(2^E*(H-2)),s⟩)
    let d := S/2^E
    H-2+d<2^w →
      d=(cross d).toNat+2 ∧ F/2^E=HighBankAdjust.adjusted H w (cross d) false := by
  dsimp only
  intro room
  have h := left_digit k B s (2^E) ready odd small low high
  dsimp only at h
  have digit : total (step^[k] ⟨B,s⟩)/2^E=(cross (total (step^[k] ⟨B,s⟩)/2^E)).toNat+2 := by
    rcases h with h|h <;> simp [total,h,cross]
  have gap : total (step^[k] ⟨B+2^k*(2^E*(H-2)),s⟩) =
      total (step^[k] ⟨B,s⟩)+2^E*(H-2) := by
    rw [long_u k B s _ ready]
    dsimp [total]
    omega
  have actual := value _ _ H w E 0 _ false (by simpa only [pow_zero,one_mul] using gap)
    far (by simpa only [pow_zero,Nat.div_one] using room) (by simp)
    (by simpa only [pow_zero,Nat.div_one,Bool.not_false,Bool.toNat_true,Nat.mul_one] using digit)
  exact ⟨digit,by simpa only [pow_zero,one_mul,Nat.mod_one,Nat.add_zero] using actual⟩

end ECDSAAdd.Entrant.StairPacket.HighBankSum

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Relocated
open Partial LeaveRelocation Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def moves : List (Wire×Wire) := [(956, 941), (957, 942), (958, 943), (959, 944), (960, 945), (961, 946), (962, 947), (963, 948), (964, 949), (965, 950), (966, 951), (967, 952), (968, 953), (969, 954), (970, 955), (971, 956), (972, 957), (973, 958), (974, 959), (975, 960), (976, 961), (977, 962), (978, 963), (979, 964), (980, 965), (981, 966), (982, 967), (983, 968), (984, 969), (985, 970), (986, 971), (987, 972), (988, 973), (989, 974), (990, 975), (991, 976), (992, 977), (993, 978), (994, 979), (995, 980), (996, 981), (997, 982), (998, 983), (999, 984), (1000, 985), (1001, 986), (1002, 987), (1003, 988), (1004, 989), (1005, 990), (1006, 991), (1007, 992), (1008, 993), (1009, 994), (1010, 995), (1011, 996), (1012, 997), (1013, 998), (1014, 999), (1015, 1000), (1016, 1001), (1017, 1002), (1018, 1003), (1019, 1004), (1020, 1005), (1021, 1006), (1022, 1007), (1023, 1008), (1024, 1009), (1025, 1010), (1026, 1011), (1027, 1012), (1028, 1013), (1029, 1014), (1030, 1015), (1031, 1016), (1032, 1017), (1033, 1018), (1034, 1019), (1035, 1020), (1036, 1021), (1037, 1022), (1038, 1023), (1039, 1024), (1040, 1025), (1041, 1026), (1042, 1027), (1598, 1028), (1599, 1029), (1600, 1030), (1601, 1031), (1602, 1032), (1603, 1033), (1604, 1034), (1605, 1035), (1606, 1036), (1607, 1037), (1608, 1038), (1609, 1039), (1610, 1040), (1611, 1041), (1612, 1042), (1557, 1713), (1558, 1714), (1723, 1715), (1721, 1716), (1725, 1717), (1724, 1718)]
def lastPart := leave225.drop 2868
def firstBack := leave225Inv.take 324
theorem emitted : lastPart=program moves := by decide +kernel
theorem inverseEmitted : firstBack=program moves.reverse := by decide +kernel
theorem properMoves : ∀p∈moves,p.1≠p.2 := by decide +kernel

theorem forward (s : State) (m : List Bool) :
    run lastPart m s=⟨s.phase,fun q=>s.basis (source moves q)⟩ := by
  rw [emitted];exact actual moves properMoves s m

theorem reverse (s : State) (m n : List Bool) : run firstBack n (run lastPart m s)=s := by
  rw [forward,inverseEmitted,actual _ (by simpa using properMoves)]
  cases s with
  | mk phase basis => exact congrArg (State.mk phase) (funext (fun q=>congrArg basis (undoSources moves q)))

theorem upperMap : ∀i:Fin 102,source moves (941+i.val)=live (10+i.val) ∧
    source moves (411+i.val)=411+i.val := by decide +kernel

theorem rails (s : State) (m : List Bool) (Z : Nat)
    (pos:∀i:Fin 102,s.basis (live (10+i.val))=Z.testBit (10+i.val))
    (zero:∀i:Fin 102,s.basis (411+i.val)=false) (i:Fin 102) :
    let v:=run lastPart m s
    v.basis (411+i.val)=false ∧ v.basis (941+i.val)=Z.testBit (10+i.val) := by
  rw [forward];simp only [(upperMap i).1,(upperMap i).2,zero i,pos i,and_self]

theorem flags (s : State) (m : List Bool) :
    let v:=run lastPart m s
    v.basis 1713=s.basis 1557 ∧ v.basis 1714=s.basis 1558 ∧ v.basis 1715=s.basis 1723 ∧ v.basis 1716=s.basis 1721 ∧ v.basis 1717=s.basis 1725 ∧ v.basis 1718=s.basis 1724 ∧ v.basis 1812=s.basis 1812 := by
  rw [forward];exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave225Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Relocated
open Partial LeaveRelocation Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def moves : List (Wire×Wire) := [(949, 934), (950, 935), (951, 936), (952, 937), (953, 938), (954, 939), (955, 940), (956, 941), (957, 942), (958, 943), (959, 944), (960, 945), (961, 946), (962, 947), (963, 948), (964, 949), (965, 950), (966, 951), (967, 952), (968, 953), (969, 954), (970, 955), (971, 956), (972, 957), (973, 958), (974, 959), (975, 960), (976, 961), (977, 962), (978, 963), (979, 964), (980, 965), (981, 966), (982, 967), (983, 968), (984, 969), (985, 970), (986, 971), (987, 972), (988, 973), (989, 974), (990, 975), (991, 976), (992, 977), (993, 978), (994, 979), (995, 980), (996, 981), (997, 982), (998, 983), (999, 984), (1000, 985), (1001, 986), (1002, 987), (1003, 988), (1004, 989), (1005, 990), (1006, 991), (1007, 992), (1008, 993), (1009, 994), (1010, 995), (1011, 996), (1012, 997), (1013, 998), (1014, 999), (1015, 1000), (1016, 1001), (1017, 1002), (1018, 1003), (1019, 1004), (1020, 1005), (1021, 1006), (1022, 1007), (1023, 1008), (1024, 1009), (1025, 1010), (1026, 1011), (1027, 1012), (1028, 1013), (1029, 1014), (1030, 1015), (1031, 1016), (1032, 1017), (1033, 1018), (1034, 1019), (1035, 1020), (1036, 1021), (1037, 1022), (1038, 1023), (1039, 1024), (1040, 1025), (1041, 1026), (1042, 1027), (1598, 1028), (1599, 1029), (1600, 1030), (1601, 1031), (1602, 1032), (1603, 1033), (1604, 1034), (1605, 1035), (1606, 1036), (1607, 1037), (1608, 1038), (1609, 1039), (1610, 1040), (1611, 1041), (1612, 1042), (1557, 1706), (1558, 1707), (1715, 1708), (1713, 1709), (1717, 1710), (1716, 1711)]
def lastPart := leave240.drop 3045
def firstBack := leave240Inv.take 345
theorem emitted : lastPart=program moves := by decide +kernel
theorem inverseEmitted : firstBack=program moves.reverse := by decide +kernel
theorem properMoves : ∀p∈moves,p.1≠p.2 := by decide +kernel

theorem forward (s : State) (m : List Bool) :
    run lastPart m s=⟨s.phase,fun q=>s.basis (source moves q)⟩ := by
  rw [emitted];exact actual moves properMoves s m

theorem reverse (s : State) (m n : List Bool) : run firstBack n (run lastPart m s)=s := by
  rw [forward,inverseEmitted,actual _ (by simpa using properMoves)]
  cases s with
  | mk phase basis => exact congrArg (State.mk phase) (funext (fun q=>congrArg basis (undoSources moves q)))

theorem upperMap : ∀i:Fin 109,source moves (934+i.val)=live (11+i.val) ∧
    source moves (419+i.val)=419+i.val := by decide +kernel

theorem rails (s : State) (m : List Bool) (Z : Nat)
    (pos:∀i:Fin 109,s.basis (live (11+i.val))=Z.testBit (11+i.val))
    (zero:∀i:Fin 109,s.basis (419+i.val)=false) (i:Fin 109) :
    let v:=run lastPart m s
    v.basis (419+i.val)=false ∧ v.basis (934+i.val)=Z.testBit (11+i.val) := by
  rw [forward];simp only [(upperMap i).1,(upperMap i).2,zero i,pos i,and_self]

theorem flags (s : State) (m : List Bool) :
    let v:=run lastPart m s
    v.basis 1706=s.basis 1557 ∧ v.basis 1707=s.basis 1558 ∧ v.basis 1708=s.basis 1715 ∧ v.basis 1709=s.basis 1713 ∧ v.basis 1710=s.basis 1717 ∧ v.basis 1711=s.basis 1716 ∧ v.basis 1812=s.basis 1812 := by
  rw [forward];exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave240Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Relocated
open Partial LeaveRelocation Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def moves : List (Wire×Wire) := [(941, 926), (942, 927), (943, 928), (944, 929), (945, 930), (946, 931), (947, 932), (948, 933), (949, 934), (950, 935), (951, 936), (952, 937), (953, 938), (954, 939), (955, 940), (956, 941), (957, 942), (958, 943), (959, 944), (960, 945), (961, 946), (962, 947), (963, 948), (964, 949), (965, 950), (966, 951), (967, 952), (968, 953), (969, 954), (970, 955), (971, 956), (972, 957), (973, 958), (974, 959), (975, 960), (976, 961), (977, 962), (978, 963), (979, 964), (980, 965), (981, 966), (982, 967), (983, 968), (984, 969), (985, 970), (986, 971), (987, 972), (988, 973), (989, 974), (990, 975), (991, 976), (992, 977), (993, 978), (994, 979), (995, 980), (996, 981), (997, 982), (998, 983), (999, 984), (1000, 985), (1001, 986), (1002, 987), (1003, 988), (1004, 989), (1005, 990), (1006, 991), (1007, 992), (1008, 993), (1009, 994), (1010, 995), (1011, 996), (1012, 997), (1013, 998), (1014, 999), (1015, 1000), (1016, 1001), (1017, 1002), (1018, 1003), (1019, 1004), (1020, 1005), (1021, 1006), (1022, 1007), (1023, 1008), (1024, 1009), (1025, 1010), (1026, 1011), (1027, 1012), (1028, 1013), (1029, 1014), (1030, 1015), (1031, 1016), (1032, 1017), (1033, 1018), (1034, 1019), (1035, 1020), (1036, 1021), (1037, 1022), (1038, 1023), (1039, 1024), (1040, 1025), (1041, 1026), (1042, 1027), (1598, 1028), (1557, 1698), (1558, 1699), (1708, 1700), (1706, 1701), (1710, 1702), (1709, 1703)]
def lastPart := leave255.drop 3183
def firstBack := leave255Inv.take 327
theorem emitted : lastPart=program moves := by decide +kernel
theorem inverseEmitted : firstBack=program moves.reverse := by decide +kernel
theorem properMoves : ∀p∈moves,p.1≠p.2 := by decide +kernel

theorem forward (s : State) (m : List Bool) :
    run lastPart m s=⟨s.phase,fun q=>s.basis (source moves q)⟩ := by
  rw [emitted];exact actual moves properMoves s m

theorem reverse (s : State) (m n : List Bool) : run firstBack n (run lastPart m s)=s := by
  rw [forward,inverseEmitted,actual _ (by simpa using properMoves)]
  cases s with
  | mk phase basis => exact congrArg (State.mk phase) (funext (fun q=>congrArg basis (undoSources moves q)))

theorem upperMap : ∀i:Fin 103,source moves (926+i.val)=live (10+i.val) ∧
    source moves (426+i.val)=426+i.val := by decide +kernel

theorem rails (s : State) (m : List Bool) (Z : Nat)
    (pos:∀i:Fin 103,s.basis (live (10+i.val))=Z.testBit (10+i.val))
    (zero:∀i:Fin 103,s.basis (426+i.val)=false) (i:Fin 103) :
    let v:=run lastPart m s
    v.basis (426+i.val)=false ∧ v.basis (926+i.val)=Z.testBit (10+i.val) := by
  rw [forward];simp only [(upperMap i).1,(upperMap i).2,zero i,pos i,and_self]

theorem flags (s : State) (m : List Bool) :
    let v:=run lastPart m s
    v.basis 1698=s.basis 1557 ∧ v.basis 1699=s.basis 1558 ∧ v.basis 1700=s.basis 1708 ∧ v.basis 1701=s.basis 1706 ∧ v.basis 1702=s.basis 1710 ∧ v.basis 1703=s.basis 1709 ∧ v.basis 1812=s.basis 1812 := by
  rw [forward];exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ECDSAAdd.Entrant.StairPacket.Leave255Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails routed cell

theorem member_cell (p:Shape) (n i r:Nat) (b:BasisState) (hr:r<n) :
    cell p (i+r) b∈readCells p i n b := by
  induction n generalizing i r with
  | zero=>omega
  | succ n ih=>
    cases r with
    | zero=>simp [readCells]
    | succ r=>
      apply List.mem_cons_of_mem
      simpa only [Nat.add_assoc,Nat.add_comm 1 r] using ih (i+1) r (by omega)

theorem not_both {a b:Bool} (h:(a,b)≠(true,true)) : (a&&b)=false:=by
  cases a <;> cases b <;> simp_all
namespace NativePack240
open ArchiveBoundary240
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
theorem prefix_kept (s:State) (e t:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run Partial.enter240 e s).basis) :
    let now:=run (routed idx 0 1) t (run Partial.enter240 e s)
    ∀i,now.basis (history i)=s.basis (history i) := by
  have f:∀i,firstUnchanged idx (history i):=by decide +kernel
  have ro:∀i,∀g∈Partial.enter240,CodecBitSliceVerify.target g≠history i:=by decide +kernel
  exact fun i=>(first_preserves idx _ odd _ t active _ (f i)).trans (preserve_readonly _ _ (ro i) s e)

theorem bank_kept (d:Bool) (s:State) (e t p:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run Partial.enter240 e s).basis) :
    let now:=run (program d) p (run (routed idx 0 1) t (run Partial.enter240 e s))
    ∀i:Fin 23,now.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by
  have f:∀i:Fin 23,firstUnchanged idx (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩):=by decide +kernel
  have ro:∀i:Fin 23,∀g∈Partial.enter240,CodecBitSliceVerify.target g≠rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩:=by decide +kernel
  have no:∀i:Fin 23,rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩∉support:=by decide +kernel
  dsimp only
  intro i
  exact (run_preserves_outside _ _ _ _ (fun h=>no i (List.mem_toFinset.mp (packs d h)))).trans
    ((first_preserves idx _ odd _ t active _ (f i)).trans (preserve_readonly _ _ (ro i) s e))
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
theorem prefix_kept (s:State) (e t:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run Partial.enter255 e s).basis) :
    let now:=run (routed idx 0 1) t (run Partial.enter255 e s)
    ∀i,now.basis (history i)=s.basis (history i) := by
  have f:∀i,firstUnchanged idx (history i):=by decide +kernel
  have ro:∀i,∀g∈Partial.enter255,CodecBitSliceVerify.target g≠history i:=by decide +kernel
  exact fun i=>(first_preserves idx _ odd _ t active _ (f i)).trans (preserve_readonly _ _ (ro i) s e)

theorem bank_kept (d:Bool) (s:State) (e t p:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run Partial.enter255 e s).basis) :
    let now:=run (program d) p (run (routed idx 0 1) t (run Partial.enter255 e s))
    ∀i:Fin 23,now.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by
  have f:∀i:Fin 23,firstUnchanged idx (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩):=by decide +kernel
  have ro:∀i:Fin 23,∀g∈Partial.enter255,CodecBitSliceVerify.target g≠rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩:=by decide +kernel
  have no:∀i:Fin 23,rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩∉support:=by decide +kernel
  dsimp only
  intro i
  exact (run_preserves_outside _ _ _ _ (fun h=>no i (List.mem_toFinset.mp (packs d h)))).trans
    ((first_preserves idx _ odd _ t active _ (f i)).trans (preserve_readonly _ _ (ro i) s e))
end NativePack255
namespace NativePack270
open ArchiveBoundary270
theorem prefixMap : ∀r:Fin 5,history ⟨2*r.val,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).a0 ∧
    history ⟨2*r.val+1,by omega⟩=windowNet sourceIdx (ports (shape sourceIdx) r).history := by decide +kernel
theorem legal_prefix (s t:State) (legal:StairArchiveRaw.legal (readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx s.basis)))
    (kept:∀i,t.basis (history i)=s.basis (history i)) : MeasuredCodec5.legalAt history t.basis := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  rw [kept,kept,(prefixMap i).1,(prefixMap i).2]
  have good:=legal _ (member_cell (shape sourceIdx) 15 0 i (mappedBasis sourceIdx s.basis) (by have h:=i.isLt;omega))
  apply not_both
  simpa only [Nat.zero_add,cell,mappedBasis] using good
end NativePack270
#print axioms NativePack255.bank_kept
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1701,1702,1703]
def dst : List Wire := [1029,1030,1031]
def pairs : List (Wire×Wire) := [(1029,1701),(1030,1702),(1031,1703)]
def stash (payload:State) (s:State) : State :=
  ⟨s.phase,fun q=>if q∈dst then payload.basis (backMap pairs q) else s.basis q⟩

theorem commutes (p:Program) (free:∀q∈dst,q∉wires p) (m:List Bool) (payload s:State):
    run p m (stash payload s)=stash payload (run p m s) := by
  have inc:=run_measured_locality p (wires p) (Finset.Subset.refl _) (stash payload s) s m rfl
    (fun q h=>by simp [stash,show q∉dst from fun eq=>free _ eq h])
  apply congrArg₂ State.mk inc.1
  funext q
  by_cases h:q∈wires p
  · simpa [stash,show q∉dst from fun eq=>free _ eq h] using inc.2 q h
  · rw [run_preserves_outside _ m _ _ h]
    simp only [stash,run_preserves_outside _ m s _ h]

theorem park (s:State) (m:List Bool) (empty:∀q∈dst,s.basis q=false) :
    run Partial.park270 m s=stash s (eraseSites src s) := by
  rw [show Partial.park270=moves pairs by rfl,moves_run _ (by decide) s m]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases dest:q∈dst
  · simp [stash,dest]
  by_cases source:q∈src
  · have toDst:∀w∈src,backMap pairs w∈dst:=by decide
    simp [stash,eraseSites,dest,source,empty _ (toDst _ source)]
  · simp only [src,List.mem_cons,List.not_mem_nil,or_false,not_or] at source
    have nod:=dest
    simp only [dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at nod
    simp [stash,eraseSites,dest,src,pairs,backMap,source.1,source.2.1,source.2.2,nod.1,nod.2.1,nod.2.2]

theorem park_undo (s:State) (m n:List Bool) : run Partial.park270Inv n (run Partial.park270 m s)=s := by
  rw [show Partial.park270=moves pairs by rfl,show Partial.park270Inv=moves pairs.reverse by rfl,moves_run _ (by decide),moves_run _ (by decide)]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases h:q∈src++dst
  · have inv:∀w∈src++dst,backMap pairs (backMap pairs.reverse w)=w:=by decide
    exact congrArg s.basis (inv _ h)
  · simp only [List.mem_append,src,dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    rcases h with ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩⟩
    simp [pairs,backMap,h1,h2,h3,h4,h5,h6]

#print axioms park_undo
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow

theorem scale (b : Nat) : limb b 15=2^15*2^(b+1) := by
  rw [limb,show b+15+1=15+(b+1) by omega,pow_add]

theorem rail (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b) (far : Shadow.far b 15 z) :
    let r := reduced b 15 z
    let D := 2^(b+1)*(high b 15 z-2)
    (2^b≤z.u → r.v=z.v ∧ z.u=r.u+2^15*D ∧ guard 15 r.v≤r.u) ∧
    (z.u<2^b → r.u=z.u ∧ z.v=r.v+2^15*D ∧ guard 15 r.u≤r.v) := by
  dsimp only
  have hr := (represented b 15 z small far).2.1
  have amount : gap b 15 z=2^15*(2^(b+1)*(high b 15 z-2)) := by rw [gap,scale];ring
  have base : 2^b≤limb b 15 := Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro h
    have sh : z.v<2^b := by omega
    rw [reduced,if_pos far,if_pos h] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl,by omega,(guard_small 15 z.v b sh).trans (by unfold limb at hr base;omega)⟩
  · intro h
    rw [reduced,if_pos far,if_neg (Nat.not_le.mpr h)] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl,by omega,(guard_small 15 z.u b h).trans (by unfold limb at hr base;omega)⟩


open HighBankSum

/-- With the short integer input and actual saved high quotient, the physical
    crossing decoder and shifted high correction give the true endpoint. -/
theorem far_result (b w : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b)
    (far : Shadow.far b 15 z) (odd : z.v%2=1) (enough : high b 15 z+1<2^w) :
    let r:=reduced b 15 z
    let S:=total (step^[15] r)
    let F:=total (step^[15] z)
    let t:=if 2^b≤z.u then 0 else wait 15 z.u
    let d:=S/2^(b+1)/2^t
    let neg:=cross d && (!(decide (2^b≤z.u)) && negative (oddBits (letters 15 r)))
    d=(cross d).toNat+2*(!neg).toNat ∧
      F/2^(b+1)=2^t*HighBankAdjust.adjusted (high b 15 z) w (cross d) neg+S/2^(b+1)%2^t := by
  let r:=reduced b 15 z
  let H:=high b 15 z
  let V:=2^(b+1)
  let D:=V*(H-2)
  have sides:=rail b z small far
  have bounds := (represented b 15 z small far).2
  rw [scale] at bounds
  have hH : 2≤H := by have : 3≤H := far;omega
  have pos : 2^b<V := by dsimp [V];rw [pow_succ];have := Nat.two_pow_pos b;omega
  dsimp only
  by_cases h : 2^b≤z.u
  · obtain ⟨eqV,eqU,guarded⟩:=sides.1 h
    have shape : z=⟨r.u+2^15*D,r.v⟩:=SkywalkNat.State.ext eqU eqV.symm
    have short : r.v<V := by dsimp [r];omega
    have rodd : r.v%2=1 := eqV ▸ odd
    have dcap := left_digit 15 r.u r.v V guarded rodd short bounds.1 bounds.2
    change total (step^[15] r)/V=2 ∨ total (step^[15] r)/V=3 at dcap
    have room : H-2+total (step^[15] r)/V<2^w := by change H+1<2^w at enough;omega
    have outcome:=HighBankSum.left 15 r.u r.v H w (b+1) guarded rodd short bounds.1 bounds.2 hH room
    rw [←shape] at outcome
    simpa only [if_pos h,decide_eq_true h,Bool.not_true,Bool.false_and,Bool.and_false,Bool.not_false,Bool.toNat_true,Nat.mul_one,pow_zero,Nat.div_one,one_mul,Nat.mod_one,Nat.add_zero] using outcome
  · obtain ⟨eqU,eqV,guarded⟩:=sides.2 (Nat.lt_of_not_ge h)
    have shape : z=⟨r.u,r.v+2^15*D⟩:=SkywalkNat.State.ext eqU.symm eqV
    have short : r.u<V := by dsimp [r];omega
    have rodd : r.v%2=1 := by change z.v=r.v+32768*D at eqV;omega
    have dcap := (right_digit 15 r.v r.u V guarded rodd short (by simpa only [Nat.add_comm r.v r.u] using bounds.1) (by simpa only [Nat.add_comm r.v r.u] using bounds.2)).1
    change total (step^[15] r)/(2^(wait 15 r.u)*V)=1 ∨ total (step^[15] r)/(2^(wait 15 r.u)*V)=2 ∨ total (step^[15] r)/(2^(wait 15 r.u)*V)=3 at dcap
    rw [Nat.mul_comm (2^_) V,←Nat.div_div_eq_div_mul] at dcap
    have room : H-2+total (step^[15] r)/V/2^(wait 15 r.u)<2^w := by change H+1<2^w at enough;omega
    have outcome:=HighBankSum.right 15 r.v r.u H w (b+1) (by decide) guarded rodd short (by simpa only [Nat.add_comm r.v r.u] using bounds.1) (by simpa only [Nat.add_comm r.v r.u] using bounds.2) hH room
    rw [←shape] at outcome
    have waits : wait 15 z.u=wait 15 r.u := congrArg (wait 15) eqU.symm
    simpa only [if_neg h,decide_eq_false h,Bool.not_false,Bool.true_and,waits] using outcome


theorem near_result (b : Nat) (z : SkywalkNat.State) (close : ¬ Shadow.far b 15 z) :
    reduced b 15 z=z ∧ total (step^[15] z)/2^(b+1)<2^18 := by
  refine ⟨by simp [reduced,close],?_⟩
  have lt : (z.u+z.v)/limb b 15<3 := Nat.lt_of_not_ge close
  have lim := (Nat.div_lt_iff_lt_mul (by unfold limb;positivity)).mp lt
  rw [scale] at lim
  have noninc := iter_sum_nonincrease 15 z
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  dsimp only [total]
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run routed cell

theorem ready_after_head (j:Fin 23) (P:Program) (s:State) (a b:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:onRails j 0 z s.basis)
    (preserve:∀t:State,∀q∈watch j,(run P b t).basis q=t.basis q) :
    onRails j 1 (SkywalkTrace.next z) (run P b (run (routed j 0 1) a s)).basis:=
  (watch_congr j _ _ (preserve _) _ (route_frame j 0 1 (by decide) z odd s a active).2).1

def physicalCells (j:Fin 23) (s:State) := readCells (shape j) 0 15 (mappedBasis j s.basis)

/-- The previous fifteen native records plus the three real flags written by Leave.
The codec row is derived from these fields. -/
structure PastFacts (j:Fin 23) (rawPorts:ArchivePortAction.Ports) (b:Nat) (z:SkywalkNat.State)
    (g sign cross:Bool) (s:State) : Prop where
  records : physicalCells j s=SkywalkTrace.trace 15 (encode g sign z.u z.v)
  far : s.basis (rawPorts 20)=decide (Shadow.far b 15 z)
  suffix : s.basis (rawPorts 21)=(decide (Shadow.far b 15 z) && afterFlags (decide (z.v<z.u)) ((physicalCells j s).take 5))
  crossed : s.basis (rawPorts 22)=(decide (Shadow.far b 15 z) && cross)

namespace NativePack240
open ArchiveBoundary240
theorem scratch_ready (x:State) (z:SkywalkRails.State) (on:onRails idx 1 z x.basis) :
    ∀i:Fin 157,23≤ i.val → x.basis (rawPorts i)=false:=by
  intro i hi
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp (scratch_carry i hi)
  rw [←eq]
  exact (regValue_zero _ _).mp on.2.2.2.1 _ hw

theorem matching (before:State) (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (small:min past.u past.v<2^144) (prior:PastFacts sourceIdx rawPorts 144 past g sign cross before) :
    let cells:=physicalCells sourceIdx before
    let f:=decide (Shadow.far 144 15 past)
    let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) f u (f && cross) q :=
  interrupted_row 144 past small odd g sign cross _ (prior.records.trans (true_records _ _ small odd _ _).symm)

attribute [local irreducible] onRails rawPorts codePorts rawBit rawCol ArchivePortAction.Frame

theorem frame_for (before out:State) (nowZ:SkywalkRails.State) (on:onRails idx 1 nowZ out.basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past g sign cross before)
    (bk:∀i:Fin 23,out.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=before.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)) :
    ∃row<63145,ArchivePortAction.Frame rawPorts raw row out := by
  let cells:=physicalCells sourceIdx before
  let f:=decide (Shadow.far 144 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  have tags:out.basis (rawPorts 20)=f ∧ out.basis (rawPorts 21)=u ∧ out.basis (rawPorts 22)=c:=
    ⟨(bk 20).trans prior.far,(bk 21).trans prior.suffix,(bk 22).trans prior.crossed⟩
  have record:∀i:Fin 157,i.val<23 → out.basis (rawPorts i)=data i:=
    observed before out (fun q=>bk ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  obtain ⟨row,lim,matchRow⟩:=matching before past g sign cross odd small prior
  exact ⟨row,lim,starting_frame rawPorts out row data matchRow record (scratch_ready out nowZ on)⟩

theorem completed_head (d:Bool) (src:State) (first pack:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:onRails idx 0 z src.basis) :
    onRails idx 1 (SkywalkTrace.next z) (run (program d) pack (run (routed idx 0 1) first src)).basis := by
  exact ready_after_head idx (program d) src first pack z odd active (fun t=>retains d false t pack)

theorem head_legal (before:State) (et first:List Bool) (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:onRails idx 0 nowZ (run Partial.enter240 et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (prior:PastFacts sourceIdx rawPorts 144 past g sign cross before) :
    MeasuredCodec5.legalAt history (run (routed idx 0 1) first (run Partial.enter240 et before)).basis := by
  apply legal_prefix before _ _ (prefix_kept before et first nowZ parity ready)
  change StairArchiveRaw.legal (physicalCells sourceIdx before)
  rw [prior.records]
  exact legal_signed 15 past g sign (by omega) odd

theorem admits (d:Bool) (before:State) (et first pack:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:onRails idx 0 nowZ (run Partial.enter240 et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past g sign cross before) :
    let src:=run (routed idx 0 1) first (run Partial.enter240 et before)
    let out:=run (program d) pack src
    MeasuredCodec5.legalAt history src.basis ∧ ∃row<63145,Frame rawPorts raw row out := by
  dsimp only
  refine ⟨head_legal before et first nowZ parity ready past g sign cross odd prior,?_⟩
  exact frame_for before _ (SkywalkTrace.next nowZ)
    (completed_head d (run Partial.enter240 et before) first pack nowZ parity ready)
    past g sign cross odd small prior (bank_kept d before et first pack nowZ parity ready)
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem scratch_ready (x:State) (z:SkywalkRails.State) (on:onRails idx 1 z x.basis) :
    ∀i:Fin 157,23≤ i.val → x.basis (rawPorts i)=false:=by
  intro i hi
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp (scratch_carry i hi)
  rw [←eq]
  exact (regValue_zero _ _).mp on.2.2.2.1 _ hw

theorem matching (before:State) (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (small:min past.u past.v<2^136) (prior:PastFacts sourceIdx rawPorts 136 past g sign cross before) :
    let cells:=physicalCells sourceIdx before
    let f:=decide (Shadow.far 136 15 past)
    let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) f u (f && cross) q :=
  interrupted_row 136 past small odd g sign cross _ (prior.records.trans (true_records _ _ small odd _ _).symm)

attribute [local irreducible] onRails rawPorts codePorts rawBit rawCol ArchivePortAction.Frame

theorem frame_for (before out:State) (nowZ:SkywalkRails.State) (on:onRails idx 1 nowZ out.basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past g sign cross before)
    (bk:∀i:Fin 23,out.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=before.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)) :
    ∃row<63145,ArchivePortAction.Frame rawPorts raw row out := by
  let cells:=physicalCells sourceIdx before
  let f:=decide (Shadow.far 136 15 past)
  let u:=f && afterFlags (decide (past.v<past.u)) (cells.take 5)
  let c:=f && cross
  let data:=rawBit (read (cells.drop 5)) f u c
  have tags:out.basis (rawPorts 20)=f ∧ out.basis (rawPorts 21)=u ∧ out.basis (rawPorts 22)=c:=
    ⟨(bk 20).trans prior.far,(bk 21).trans prior.suffix,(bk 22).trans prior.crossed⟩
  have record:∀i:Fin 157,i.val<23 → out.basis (rawPorts i)=data i:=
    observed before out (fun q=>bk ⟨q,Nat.lt_trans q.isLt (by decide : 20<23)⟩) f u c tags
  obtain ⟨row,lim,matchRow⟩:=matching before past g sign cross odd small prior
  exact ⟨row,lim,starting_frame rawPorts out row data matchRow record (scratch_ready out nowZ on)⟩

theorem completed_head (d:Bool) (src:State) (first pack:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:onRails idx 0 z src.basis) :
    onRails idx 1 (SkywalkTrace.next z) (run (program d) pack (run (routed idx 0 1) first src)).basis := by
  exact ready_after_head idx (program d) src first pack z odd active (fun t=>retains d false t pack)

theorem head_legal (before:State) (et first:List Bool) (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:onRails idx 0 nowZ (run Partial.enter255 et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1)
    (prior:PastFacts sourceIdx rawPorts 136 past g sign cross before) :
    MeasuredCodec5.legalAt history (run (routed idx 0 1) first (run Partial.enter255 et before)).basis := by
  apply legal_prefix before _ _ (prefix_kept before et first nowZ parity ready)
  change StairArchiveRaw.legal (physicalCells sourceIdx before)
  rw [prior.records]
  exact legal_signed 15 past g sign (by omega) odd

theorem admits (d:Bool) (before:State) (et first pack:List Bool)
    (nowZ:SkywalkRails.State) (parity:(nowZ.a+nowZ.b)%2=1)
    (ready:onRails idx 0 nowZ (run Partial.enter255 et before).basis)
    (past:SkywalkNat.State) (g sign cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past g sign cross before) :
    let src:=run (routed idx 0 1) first (run Partial.enter255 et before)
    let out:=run (program d) pack src
    MeasuredCodec5.legalAt history src.basis ∧ ∃row<63145,Frame rawPorts raw row out := by
  dsimp only
  refine ⟨head_legal before et first nowZ parity ready past g sign cross odd prior,?_⟩
  exact frame_for before _ (SkywalkTrace.next nowZ)
    (completed_head d (run Partial.enter255 et before) first pack nowZ parity ready)
    past g sign cross odd small prior (bank_kept d before et first pack nowZ parity ready)
end NativePack255
#print axioms NativePack255.admits
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed Portal270Flag
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
def misses (i:Instr) := decide (1029∉i.wires ∧ 1030∉i.wires ∧ 1031∉i.wires)
theorem misses_all (P:Program) (h:P.all misses=true) : ∀q∈dst,q∉wires P:=by
  intro q hq
  induction P with
  | nil=>simp [wires]
  | cons i P ih=>
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hi:1029∉i.wires ∧ 1030∉i.wires ∧ 1031∉i.wires:=of_decide_eq_true h.1
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨by rcases List.mem_cons.mp hq with rfl|h'
              · exact hi.1
              · rcases List.mem_cons.mp h' with rfl|h''
                · exact hi.2.1
                · obtain rfl:=List.mem_singleton.mp h'';exact hi.2.2,ih h.2⟩
theorem avoid : ∀q∈dst,q∉wires Partial.portal270:=misses_all _ (by decide +kernel)
theorem avoidInv : ∀q∈dst,q∉wires Partial.portal270Inv:=misses_all _ (by decide +kernel)

theorem parked_release (z:SkywalkNat.State) (small:min z.u z.v<2^121) (raw s:State) (m n:List Bool)
    (route sg:Bool)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative sg z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u))
      (pullState (OB5.sig 269) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) :
    let out:=run Partial.portal270Inv n (run Partial.park270 m s)
    out=stash s (pullState (OB5.sig 269) raw) ∧ ∀a b,
      run Partial.park270Inv b (run Partial.portal270 a out)=s := by
  have fw (a:List Bool):=cut.unique (physical_frame_local z small raw a route sg input)
  have endEq:run Partial.portal270Inv n (run Partial.park270 m s)=stash s (pullState (OB5.sig 269) raw):=by
    rw [park _ _ empty,commutes _ avoidInv,release z small raw _ n route sg input cut]
  refine ⟨endEq,?_⟩
  intro a b
  rw [endEq,commutes _ avoid,←fw,←park s m empty,park_undo]
#print axioms parked_release
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open IntegerHigh SkywalkNat Shadow HighBankSum

def actualMode (b : Nat) (z : SkywalkNat.State) := farMode (decide (far b 15 z)) (decide (2^b≤z.u)) z.u
def place (b : Nat) (z : SkywalkNat.State) := if 2^b≤z.u then 0 else wait 15 z.u

theorem modeKey (b : Nat) (z : SkywalkNat.State) (f : far b 15 z) :
    key (actualMode b z)=place b z ∧ right (actualMode b z)= !decide (2^b≤z.u) ∧ enabled (actualMode b z)=true := by
  by_cases h : 2^b≤z.u <;> simp [actualMode,farMode,ofFlags,key,place,right,enabled,f,h]

theorem trueControls (b w : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b)
    (odd : z.v%2=1) (room : high b 15 z+1<2^w) (p : Ports) (v : BasisState)
    (bits : ∀i<16,v (p.u+i)=((total (step^[15] (reduced b 15 z)))/2^(b+1)).testBit i)
    (par : parityBits p v=oddBits (letters 15 (reduced b 15 z))) :
    let k:=actualMode b z
    let X:=total (step^[15] (reduced b 15 z))/2^(b+1)
    let d:=X/2^(place b z)
    (crossing p k).read v=(if far b 15 z then cross d else false) ∧
      (far b 15 z → (signExpr p k).read v=(!(decide (2^b≤z.u)) && negative (oddBits (letters 15 (reduced b 15 z))))) := by
  dsimp only
  by_cases f : far b 15 z
  · obtain ⟨idx,side,active⟩:=modeKey b z f
    have fit : place b z<16 := by unfold place; have h:=wait_le 15 z.u; split <;> omega
    have val:=LeaveShadowRails.far_result b w z small f odd room
    let X:=total (step^[15] (reduced b 15 z))/2^(b+1)
    let d:=X/2^(place b z)
    constructor
    · rw [crossing,active,if_pos rfl,Expr.read,idx,bits _ fit,if_pos f]
      change X.testBit (place b z)=cross d
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (d%2=1)=cross d
      have digit : d=(cross d).toNat+2*_ := val.1
      cases e : cross d <;> rw [e] at digit <;> simp only [Bool.toNat_false,Bool.toNat_true] at digit <;>
        apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq,Bool.false_eq_true,iff_false,iff_true] <;> omega
    · intro _
      rw [sign_value _ _ _ (by
        intro hs
        rw [side] at hs
        have h : z.u<2^b := by by_contra! hh;simp [hh] at hs
        have rails:=(LeaveShadowRails.rail b z small f).2 h
        rw [par]
        have eq : reduced b 15 z=⟨z.u,(reduced b 15 z).v⟩:=SkywalkNat.State.ext rails.1 rfl
        have g:=rails.2.2
        rw [rails.1] at g
        rw [eq,lead_wait 15 _ _ g,idx,place,if_neg (Nat.not_le.mpr h)]) ,side,par]
  · simp [actualMode,farMode,ofFlags,enabled,crossing,Expr.read,f]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run onRails routed unrouted

theorem unmask (P Q:Program) (tags:List Wire) (a:∀q∈tags,q∉wires P) (b:∀q∈tags,q∉wires Q)
    (s:State) (m n:List Bool) (undo:run Q n (run P m (eraseSites tags s))=eraseSites tags s) :
    run Q n (run P m s)=s := by
  rw [erase_run _ P a,erase_run _ Q b] at undo
  apply congrArg₂ State.mk (congrArg State.phase undo)
  funext q
  by_cases h:q∈tags
  · exact (run_preserves_outside Q n _ _ (b _ h)).trans (run_preserves_outside P m s _ (a _ h))
  · simpa [eraseSites,h] using congrArg (fun x:State=>x.basis q) undo
namespace NativePack240
open ArchiveBoundary240
def nextWindow (d:Bool) := Partial.enter240 ++ window d
def nextUnwind (d:Bool) := unwind d ++ Partial.enter240Inv

theorem next_window (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    let T:=Shadow.reduced 136 15 z
    out.phase=s.phase ∧ onRails idx 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind d) t out=s := by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨legal,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have all:=window_run d pre tape Z parity ready.2.1 legal row limit frame
  dsimp only [nextWindow,nextUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records 136 z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  have free:∀q∈Enter240.pending,q∉wires Partial.enter240Inv:=by decide +kernel
  apply unmask Partial.enter240 Partial.enter240Inv Enter240.pending Enter240.avoid_enter free
  exact return_packed Enter240.layout map240 _ _ inc240 (fun _=>rfl) rfl emitted240 emitted240Inv raw _ z G S small cut input _ _
end NativePack240
namespace NativePack255
open ArchiveBoundary255
def nextWindow (d:Bool) := Partial.enter255 ++ window d
def nextUnwind (d:Bool) := unwind d ++ Partial.enter255Inv

theorem next_window (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    let T:=Shadow.reduced 129 15 z
    out.phase=s.phase ∧ onRails idx 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind d) t out=s := by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨legal,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have all:=window_run d pre tape Z parity ready.2.1 legal row limit frame
  dsimp only [nextWindow,nextUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records 129 z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  have free:∀q∈Enter255.pending,q∉wires Partial.enter255Inv:=by decide +kernel
  apply unmask Partial.enter255 Partial.enter255Inv Enter255.pending Enter255.avoid_enter free
  exact return_packed Enter255.layout map255 _ _ inc255 (fun _=>rfl) rfl emitted255 emitted255Inv raw _ z G S small cut input _ _
end NativePack255
#print axioms NativePack255.next_window
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
theorem released : ∀q∈dst,OB5.sig 269 q∈(W.compactSkywalkSignPoolB base 270).released := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeavePendingHistory
open StairArchiveTrace LeaveSelector IntegerHigh

theorem traceFlags (u : Bool) (xs : List (Bool×Bool)) (n : Nat) (ok : chain u xs) :
    afterFlags u (xs.take n)=(u || (xs.take n).any Prod.snd) := by
  induction n generalizing u xs with
  | zero => simp [afterFlags]
  | succ n ih =>
    cases xs with
    | nil => simp [afterFlags]
    | cons x xs =>
      change afterFlags (u || !x.1) (xs.take n)=_
      rw [ih _ _ ok.2]
      simp only [List.take_succ_cons,List.any_cons,ok.1]
      cases u <;> cases x.1 <;> simp

theorem initialTrue (xs : List (Bool×Bool)) (ok : chain true xs) (n : Nat) :
    (xs.take n).any Prod.snd=false := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.take_succ_cons,List.any_cons,ok.1,Bool.not_true,Bool.false_and,Bool.false_or]
      exact ih _ (by simpa only [Bool.true_or] using ok.2)

theorem firstBits (xs : List Bool) (n : Nat) (hn : n≤xs.length) :
    (xs.take n).any id=decide (xs.idxOf true<n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      cases x <;> simp [ih xs (by simpa using hn)]

/-- In far mode the pending suffix flag records the orientation after five
    events. Erasing the previous orientation uses precisely the same event bits. -/
theorem flags (u : Bool) (xs : List (Bool×Bool)) (ok : chain u xs) (len : 5≤xs.length)
    (w : Fin 16) (index : u=false → (xs.map Prod.snd).idxOf true=w.val) :
    let k:=ofFlags true u w
    nearby k=afterFlags u (xs.take 5) ∧ (u ^^ (nearby k && !((xs.take 5).any Prod.snd)))=false := by
  have word:=firstBits (xs.map Prod.snd) 5 (by simpa using len)
  rw [←List.map_take,List.any_map] at word
  change (xs.take 5).any Prod.snd=decide ((xs.map Prod.snd).idxOf true<5) at word
  cases u with
  | true =>
    simp only [traceFlags true xs 5 ok,initialTrue xs ok 5]
    simp [ofFlags,nearby,enabled,key]
  | false =>
    rw [index rfl] at word
    simp only [traceFlags false xs 5 ok,word]
    simp [ofFlags,nearby,enabled,key]


theorem firstExchangeIndex (xs : List (Bool×Bool)) (k : Nat) (bound : k≤xs.length)
    (read : ∀i (h:i<xs.length),i≤k → xs[i].2=decide (i=k)) :
    (xs.map Prod.snd).idxOf true=k := by
  induction xs generalizing k with
  | nil => simp at bound; simp [bound]
  | cons p ps ih =>
    cases k with
    | zero =>
      have first:=read 0 (by simp) (by omega)
      have on:p.2=true:=by simpa using first
      simp [on]
    | succ k =>
      have first:p.2=false:=by simpa using read 0 (by simp) (by omega)
      have rest:=ih k (by simpa using bound) (fun i h early=>by
        simpa only [List.getElem_cons_succ,Nat.succ.injEq] using read (i+1) (by simpa using h) (by omega))
      simp [first,rest]


theorem pending (f u : Bool) (xs : List (Bool×Bool)) (w : Fin 16) (len : xs.length=15)
    (ok : f=true → chain u xs)
    (read : f=true → u=false → ∀i (h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val)) :
    let n:=nearby (ofFlags f u w)
    n=(f && afterFlags u (xs.take 5)) ∧
      ((f && u) ^^ (n && !(xs.take 5).any Prod.snd))=false := by
  cases f with
  | false => simp [nearby,ofFlags,enabled]
  | true =>
    have b : w.val≤xs.length := by rw [len];have h:=w.isLt;omega
    exact flags u xs (ok rfl) (by omega) w (fun off => firstExchangeIndex xs w.val b (read rfl off))

end ECDSAAdd.Entrant.StairPacket.LeavePendingHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem dormant (i:Nat) (d:Bool) (seed p:Nat) (raw:State) (q:Wire)
    (stage:Rolling1588.Integer.Stage base d seed p i raw.basis)
    (outside:q∉wires (Rolling1588.Integer.encodePrefix base d i))
    (inHigh:q∈(W.compactSkywalkSignPoolB base i).released) : raw.basis q=false := by
  obtain ⟨s,hs,eq⟩:=stage
  have clean:(W.compactSkywalkSignPoolB base i).Clean s.basis:=hs.2.2
  rw [eq,run_preserves_outside _ _ s q outside]
  exact clean q inHigh
theorem above_history (i:Nat) (lim:i≤512) (d:Bool) (q:Nat)
    (q0:i+16<q) (q1:q<1044) : q∉wires (Rolling1588.Integer.encodePrefix base d i):=by
  rw [Rolling1588.Integer.prefix_support_eq]
  intro mem
  obtain ⟨j,where',side⟩:=StackOB5Base.encodePrefix_mem i lim _ mem
  change q=j+16 at where'
  omega
theorem clear_dest (d:Bool) (seed p:Nat) (raw:State)
    (stage:Rolling1588.Integer.Stage base d seed p 270 raw.basis) :
    ∀q∈dst,(pullState (OB5.sig 269) raw).basis q=false:=by
  have bounds:∀q∈dst,270+16<OB5.sig 269 q ∧ OB5.sig 269 q<1044:=by decide +kernel
  intro q hit
  exact dormant 270 d seed p raw (OB5.sig 269 q) stage
    (above_history 270 (by decide) d _ (bounds _ hit).1 (bounds _ hit).2) (released _ hit)
#print axioms clear_dest
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 270
def P:=TickRanges.tick base 270
def Q:=W.ReverseCarry.compactReceiverTick base 270
def physP:=renameProgram (OB5.sig 270) P
def physQ:=renameProgram (OB5.sig 270) Q
theorem supports : wires P⊆L.wires.toFinset ∧ wires Q⊆L.wires.toFinset :=
  ⟨(TickRanges.tick_support base 270 (by decide) base_pool_nodup).trans
    (W.repairedTick_support base 270 (by decide) base_pool_nodup),
    W.ReverseCarry.compactReceiverTick_support base 270 (by decide) base_pool_nodup⟩
theorem physical_free (R:Program) (sub:wires R⊆L.wires.toFinset) (q:Wire)
    (off:OB5.sig 270 q∉L.wires) : q∉wires (renameProgram (OB5.sig 270) R) := by
  rw [JointForward1588.wires_rename_image]
  intro h
  obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
  rw [OB5.sig_invol 270 (by decide)] at off
  exact off (List.mem_toFinset.mp (sub mem))
theorem spared : ∀q∈ParkEndpoint.dst,OB5.sig 270 q∉L.wires := by decide +kernel
theorem stashP : ∀q∈ParkEndpoint.dst,q∉wires physP := fun q hit=>physical_free P supports.1 q (spared q hit)
theorem stashQ : ∀q∈ParkEndpoint.dst,q∉wires physQ := fun q hit=>physical_free Q supports.2 q (spared q hit)
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic
theorem input_agree (L:SkywalkIntegerLayout) (A B:Int) (G:Bool) (s t:BasisState)
    (a:SkywalkIntegerInput L A B G s) (b:SkywalkIntegerInput L A B G t) :
    ∀q∈L.wires,s q=t q:=by
  obtain ⟨a1,a2,a3,a4,a5,a6⟩:=a
  obtain ⟨b1,b2,b3,b4,b5,b6⟩:=b
  have left:=(signedRegValue_eq_iff _ _ _).mp (a1.trans b1.symm)
  have right:=(signedRegValue_eq_iff _ _ _).mp (a2.trans b2.symm)
  have cs:=(regValue_zero _ _).mp a6
  have ct:=(regValue_zero _ _).mp b6
  intro q hit
  have choices:q∈L.a ∨ q∈L.b ∨ q=L.previous ∨ q=L.ext ∨ q=L.history ∨ q∈L.carry:=by
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.a,SkywalkIntegerLayout.b,List.mem_cons,List.mem_append] at *
    tauto
  rcases choices with h|h|rfl|rfl|rfl|h
  · exact left _ h
  · exact right _ h
  · exact a3.trans b3.symm
  · exact a4.trans b4.symm
  · exact a5.trans b5.symm
  · exact (cs _ h).trans (ct _ h).symm
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic Secp256k1 MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem local_reference (i:Nat) (hi:i<512) (d:Bool) (x:Nat) (original:State)
    (stage:Rolling1588.Integer.Stage base d x p i original.basis) :
    ∃raw:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
      ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset, original.basis q=raw.basis q := by
  obtain ⟨raw,hraw,eq⟩:=stage
  refine ⟨raw,hraw,fun q hq=>?_⟩
  rw [eq]
  exact run_preserves_outside _ _ _ q (fun used=>Finset.disjoint_left.mp
    (Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i i (le_refl _) hi) used hq)

theorem undo_on_domain (w:Nat→Wire) (hn:(skywalkPoolWires w).Nodup) (x p i:Nat)
    (hi:i<512) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hgap:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p)
    (t raw:State) (a b:List Bool)
    (hraw:W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis)
    (read:∀q∈(W.compactSkywalkTickLayout w i).wires,t.basis q=raw.basis q) :
    run (W.ReverseCarry.compactReceiverTick w i) b (run (W.compactSkywalkTick w i) a t)=t:=by
  have loc := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx hc hi raw hraw
  have hh : t.basis (W.compactSkywalkTickLayout w i).history=false := by
    rw [read _ (by simp [SkywalkIntegerLayout.wires])]
    exact loc.2.2.2.2.1
  have tops : W.trimTick i →
      t.basis (w (i+W.compactSkywalkTickPreWidth i-1))=t.basis (w (i+W.compactSkywalkTickPreWidth i-2)) ∧
      t.basis (w (770+W.compactSkywalkTickPreWidth i-1))=t.basis (w (770+W.compactSkywalkTickPreWidth i-2)) := by
    intro htr
    have st := W.compactSkywalkStage_tops w hn x p i hp0 hx0 hpo hp hgap hx hc hi htr raw hraw
    have split := W.compactSkywalkTick_aMid_split w i hi
    have mem (q : Wire) (h : q∈(W.compactSkywalkTickLayout w i).aMid ∨ q=(W.compactSkywalkTickLayout w i).aSign ∨
        q∈(W.compactSkywalkTickLayout w i).bMid ∨ q=(W.compactSkywalkTickLayout w i).bSign) :
        q∈(W.compactSkywalkTickLayout w i).wires := by
      simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
        List.mem_cons,List.mem_append]
      itauto
    have ra := read _ (mem _ (Or.inr (Or.inl rfl)))
    have rb := read _ (mem _ (Or.inr (Or.inr (Or.inr rfl))))
    have la := read (w (i+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inl (by rw [split.1]; simp)))
    have lb := read (w (770+W.compactSkywalkTickPreWidth i-2))
      (mem _ (Or.inr (Or.inr (Or.inl (by rw [split.2]; simp)))))
    simp only [W.compactSkywalkTickLayout] at ra rb
    exact ⟨by rw [ra,la]; exact st.1,by rw [rb,lb]; exact st.2⟩
  have clean : regValue (W.compactSkywalkTickLayout w i).carry t.basis=0 := by
    rw [regValue_congr _ t.basis raw.basis (by
      intro q hq
      exact read q (by simp only [SkywalkIntegerLayout.wires,List.mem_append,List.mem_cons]; itauto))]
    exact loc.2.2.2.2.2
  exact W.ReverseCarry.compactReceiverTick_roundtrip w i hi hn t a b hh clean tops
#print axioms undo_on_domain
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def canonical:= W.compactSkywalkTick base 270
def Reads (a b:State) := ∀q∈L.wires.toFinset,a.basis q=b.basis q
theorem apply_old (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis) (a b:List Bool) :
    run P a actual=run canonical b actual:=by
  obtain ⟨w,sw,agree⟩:=Rolling1588.Integer.old_stage_local base d base_pool_nodup x p 270 (by decide) original stage
  have old:=TickRanges.tick_eq5 x hx0 hx 270 (by decide) w a sw
  have same:=Stack5.local_replace P (W.repairedTick base 270) L.wires.toFinset supports.1
    (W.repairedTick_support base 270 (by decide) base_pool_nodup) original w a a agree old
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have reference:=Rolling1588.Integer.repaired_eq base d base_pool_nodup x p 270 hp0 hx0 hpo hp gap hx cop (by decide) original a b stage
  exact Stack5.local_replace P canonical L.wires.toFinset supports.1
    (W.compactSkywalkTick_support base 270 (by decide) base_pool_nodup) actual original a b read (same.trans reference)

theorem compact_undo (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis) (a b:List Bool) :
    run Q b (run canonical a actual)=actual:=by
  obtain ⟨ref,stock,agree⟩:=local_reference 270 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  exact undo_on_domain base base_pool_nodup x p 270 (by decide) hp0 hx0 hpo hp gap hx cop actual ref a b stock
    (fun q h=>(read _ (List.mem_toFinset.mpr h)).trans (agree _ (List.mem_toFinset.mpr h)))
#print axioms apply_old
#print axioms compact_undo
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem physical (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State)
    (read:Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false)
    (m:List Bool) :
    let start:=ParkEndpoint.stash tags (pullState (OB5.sig 269) raw)
    let out:=run physP m start
    out=ParkEndpoint.stash tags (pullState (OB5.sig 270) (run canonical [] raw)) ∧
      ∀t,run physQ t out=start := by
  have pre:pullState (OB5.sig 269) raw=pullState (OB5.sig 270) raw:=
    OB5.pull_step 270 (by decide) raw hist (fun _=>swapSlot)
  have result:run physP m (ParkEndpoint.stash tags (pullState (OB5.sig 269) raw))=
      ParkEndpoint.stash tags (pullState (OB5.sig 270) (run canonical [] raw)):=by
    rw [ParkEndpoint.commutes _ stashP,pre,physP,OB5.run_rename _ (by decide),apply_old d x hx0 hx raw original read stage m []]
  refine ⟨result,?_⟩
  intro t
  rw [result,ParkEndpoint.commutes _ stashQ,physQ,OB5.run_rename _ (by decide),compact_undo d x hx0 hx raw original read stage,←pre]
#print axioms physical
end ECDSAAdd.Entrant.StairPacket.EndTick

end

