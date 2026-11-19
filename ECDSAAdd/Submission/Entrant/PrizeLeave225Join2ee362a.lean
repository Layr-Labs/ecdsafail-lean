import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Arithmetic.SkywalkIntegerTick
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeStair44PointMap486a9e3
import ECDSAAdd.Submission.Entrant.PrizeStairArchiveEnter09fd522f

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Join
open HighBankJoin Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def tags : List Wire := [1576, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]
def columns : List Column := [
  ⟨true,some 1576,401,1718⟩, ⟨true,some 1562,402,1719⟩, ⟨true,some 1563,403,1720⟩, ⟨true,some 1564,404,949⟩, ⟨true,some 1565,405,950⟩, ⟨true,some 1566,406,951⟩, ⟨true,some 1567,407,952⟩, ⟨true,some 1568,408,953⟩, ⟨true,some 1569,409,954⟩, ⟨true,some 1570,410,955⟩, ⟨false,some 1571,411,956⟩, ⟨false,some 1572,412,957⟩, ⟨false,some 1573,413,958⟩, ⟨false,some 1574,414,959⟩, ⟨false,some 1575,415,960⟩, ⟨false,some 1560,416,961⟩, ⟨false,none,417,962⟩, ⟨false,none,418,963⟩]

def digitPass := digits (tags.getD · 0) (fun j => 401+j) 1724 1613 0 16
def wordPass := word 1614 columns

theorem emitted : ((leave225.drop 2080).take 108) = digitPass ++ wordPass := by rfl

theorem sites : WellPlaced 1614 columns := by
  unfold WellPlaced
  decide +kernel

theorem disjoint : columns.Pairwise Apart := by
  unfold Apart
  decide +kernel

theorem digitSites : DigitLayout (tags.getD · 0) (fun j => 401+j) 1724 1613 0 16 := by
  have valid : ∀ i : Fin 16, [tags.getD i 0, 1724, 1613, 401+i.val, 401+(i.val+1)].Nodup := by decide +kernel
  have separate : ∀ i : Fin 16, ∀ j : Fin 17, tags.getD i 0 ≠ 401+j.val := by decide +kernel
  exact ⟨fun i _ hi => valid ⟨i,hi⟩,fun i _ hi j _ hj => separate ⟨i,hi⟩ ⟨j,by omega⟩⟩

theorem assembled :
    leave225 = leave225.take 2080 ++ ((digitPass ++ wordPass) ++ leave225.drop 2188) := by
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave225Join

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Join
open HighBankJoin Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def tags : List Wire := [1576, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]
def columns : List Column := [
  ⟨true,some 1576,408,1710⟩, ⟨true,some 1562,409,1711⟩, ⟨true,some 1563,410,1712⟩, ⟨true,some 1564,411,941⟩, ⟨true,some 1565,412,942⟩, ⟨true,some 1566,413,943⟩, ⟨true,some 1567,414,944⟩, ⟨true,some 1568,415,945⟩, ⟨true,some 1569,416,946⟩, ⟨true,some 1570,417,947⟩, ⟨true,some 1571,418,948⟩, ⟨false,some 1572,419,949⟩, ⟨false,some 1573,420,950⟩, ⟨false,some 1574,421,951⟩, ⟨false,some 1575,422,952⟩, ⟨false,some 1560,423,953⟩, ⟨false,none,424,954⟩, ⟨false,none,425,955⟩]

def digitPass := digits (tags.getD · 0) (fun j => 408+j) 1716 1613 0 16
def wordPass := word 1614 columns

theorem emitted : ((leave240.drop 2216).take 107) = digitPass ++ wordPass := by rfl

theorem sites : WellPlaced 1614 columns := by
  unfold WellPlaced
  decide +kernel

theorem disjoint : columns.Pairwise Apart := by
  unfold Apart
  decide +kernel

theorem digitSites : DigitLayout (tags.getD · 0) (fun j => 408+j) 1716 1613 0 16 := by
  have valid : ∀ i : Fin 16, [tags.getD i 0, 1716, 1613, 408+i.val, 408+(i.val+1)].Nodup := by decide +kernel
  have separate : ∀ i : Fin 16, ∀ j : Fin 17, tags.getD i 0 ≠ 408+j.val := by decide +kernel
  exact ⟨fun i _ hi => valid ⟨i,hi⟩,fun i _ hi j _ hj => separate ⟨i,hi⟩ ⟨j,by omega⟩⟩

theorem assembled :
    leave240 = leave240.take 2216 ++ ((digitPass ++ wordPass) ++ leave240.drop 2323) := by
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave240Join

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterLimb

def guardWord (m h w : Nat) (far long : Bool) :=
  let a:=h%8
  let na:=if far then 2 else a
  (((((m%8+w)%8) ^^^ (if long then a else 0) ^^^ (if long then na else 0))+8-w)%8)

/-- A far numerator loses an exact multiple of U. Its low limb is intact and
its next digit is two. A far denominator receives the identical decrement
exactly when the long coordinate is u. -/
theorem limbs (U X M w : Nat) (positive:0<U) (bw:w≤1) (long:Bool)
    (far:3≤X/U) (same:long=true → X/U=M/U+w) :
    let d:=(X/U-2)*U
    (X-d)%U=X%U ∧ (X-d)/U=2 ∧
    (M-(if long then d else 0))%U=M%U ∧
    ((M-(if long then d else 0))/U)%8=guardWord (M/U) (X/U) w true long := by
  let H:=X/U
  let D:=(H-2)*U
  have hx:=Nat.mod_add_div X U
  have xm:=Nat.mod_lt X positive
  have splitX:U*H=D+U*2 := by
    change U*H=(H-2)*U+U*2
    rw [Nat.mul_comm (H-2) U,←Nat.mul_add,show H-2+2=H by change 3≤H at far;omega]
  have rx:X-D=X%U+U*2:=by change X%U+U*H=X at hx;omega
  dsimp only
  change (X-D)%U=X%U ∧ (X-D)/U=2 ∧ _
  rw [rx,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt xm,Nat.zero_add]
  refine ⟨rfl,rfl,?_⟩
  cases long with
  | false =>
    simp [guardWord,Nat.add_mod]
    omega
  | true =>
    have eq:H=M/U+w:=same rfl
    have ym:=Nat.mod_lt M positive
    have hy:=Nat.mod_add_div M U
    have q:M/U=(H-2)+(2-w):=by change 3≤H at far; omega
    have splitM:U*(M/U)=D+U*(2-w) := by rw [q,Nat.mul_add,Nat.mul_comm U (H-2)]
    have ry:M-D=M%U+U*(2-w):=by omega
    change (M-D)%U=M%U ∧ ((M-D)/U)%8=_
    rw [ry,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt ym,Nat.zero_add]
    refine ⟨rfl,?_⟩
    have eqMod:((M/U)%8+w)%8=H%8:=by rw [eq,Nat.mod_add_mod]
    change (2-w)%8=(((M/U%8+w)%8 ^^^ H%8 ^^^ 2)+8-w)%8
    rw [eqMod,Nat.xor_self,Nat.zero_xor]
    omega

theorem unchanged (M H w : Nat) (bw:w≤1) (long:Bool) :
    guardWord M H w false long=M%8 := by
  cases long <;> simp [guardWord] <;> omega

#print axioms limbs
#print axioms unchanged
end ECDSAAdd.Entrant.StairPacket.EnterLimb

end


section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Shift
open Partial HighBankLookup
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def bank0 : List Wire := [1718, 1719, 1720, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598]

theorem pass0 : ((leave225.drop 825).take 291) = HighBankShift.program 1613 (bank0.getD · 0) 1 97 := by rfl

theorem layout0 : HighBankShift.Layout 1613 (bank0.getD · 0) 98 := by
  apply lookupLayout
  all_goals decide +kernel

def bank1 : List Wire := [1718, 1719, 1720, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600]

theorem pass1 : ((leave225.drop 1132).take 294) = HighBankShift.program 1613 (bank1.getD · 0) 2 98 := by rfl

theorem layout1 : HighBankShift.Layout 1613 (bank1.getD · 0) 100 := by
  apply lookupLayout
  all_goals decide +kernel

def bank2 : List Wire := [1718, 1719, 1720, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600, 1601, 1602, 1603, 1604]

theorem pass2 : ((leave225.drop 1442).take 300) = HighBankShift.program 1613 (bank2.getD · 0) 4 100 := by rfl

theorem layout2 : HighBankShift.Layout 1613 (bank2.getD · 0) 104 := by
  apply lookupLayout
  all_goals decide +kernel

def bank3 : List Wire := [1718, 1719, 1720, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612]

theorem pass3 : ((leave225.drop 1758).take 312) = HighBankShift.program 1613 (bank3.getD · 0) 8 104 := by rfl

theorem layout3 : HighBankShift.Layout 1613 (bank3.getD · 0) 112 := by
  apply lookupLayout
  all_goals decide +kernel

theorem assembled : leave225 =
    ((leave225.drop 0).take 825) ++
    HighBankShift.program 1613 (bank0.getD · 0) 1 97 ++
    ((leave225.drop 1116).take 16) ++
    HighBankShift.program 1613 (bank1.getD · 0) 2 98 ++
    ((leave225.drop 1426).take 16) ++
    HighBankShift.program 1613 (bank2.getD · 0) 4 100 ++
    ((leave225.drop 1742).take 16) ++
    HighBankShift.program 1613 (bank3.getD · 0) 8 104 ++
    ((leave225.drop 2070).take 10) ++
    (Leave225Join.digitPass ++ Leave225Join.wordPass) ++
    leave225.drop 2188 := by
  rw [← pass0, ← pass1, ← pass2, ← pass3, ← Leave225Join.emitted]
  simp only [List.append_assoc]
  rw [mergeSlice leave225 2080 108, mergeSlice leave225 2070 10, mergeSlice leave225 1758 312, mergeSlice leave225 1742 16, mergeSlice leave225 1442 300, mergeSlice leave225 1426 16, mergeSlice leave225 1132 294, mergeSlice leave225 1116 16, mergeSlice leave225 825 291, mergeSlice leave225 0 825, List.drop_zero]

end ECDSAAdd.Entrant.StairPacket.Leave225Shift

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Shift
open Partial HighBankLookup
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def bank0 : List Wire := [1710, 1711, 1712, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598]

theorem pass0 : ((leave240.drop 865).take 315) = HighBankShift.program 1613 (bank0.getD · 0) 1 105 := by rfl

theorem layout0 : HighBankShift.Layout 1613 (bank0.getD · 0) 106 := by
  apply lookupLayout
  all_goals decide +kernel

def bank1 : List Wire := [1710, 1711, 1712, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600]

theorem pass1 : ((leave240.drop 1196).take 318) = HighBankShift.program 1613 (bank1.getD · 0) 2 106 := by rfl

theorem layout1 : HighBankShift.Layout 1613 (bank1.getD · 0) 108 := by
  apply lookupLayout
  all_goals decide +kernel

def bank2 : List Wire := [1710, 1711, 1712, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600, 1601, 1602, 1603, 1604]

theorem pass2 : ((leave240.drop 1530).take 324) = HighBankShift.program 1613 (bank2.getD · 0) 4 108 := by rfl

theorem layout2 : HighBankShift.Layout 1613 (bank2.getD · 0) 112 := by
  apply lookupLayout
  all_goals decide +kernel

def bank3 : List Wire := [1710, 1711, 1712, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612]

theorem pass3 : ((leave240.drop 1870).take 336) = HighBankShift.program 1613 (bank3.getD · 0) 8 112 := by rfl

theorem layout3 : HighBankShift.Layout 1613 (bank3.getD · 0) 120 := by
  apply lookupLayout
  all_goals decide +kernel

theorem assembled : leave240 =
    ((leave240.drop 0).take 865) ++
    HighBankShift.program 1613 (bank0.getD · 0) 1 105 ++
    ((leave240.drop 1180).take 16) ++
    HighBankShift.program 1613 (bank1.getD · 0) 2 106 ++
    ((leave240.drop 1514).take 16) ++
    HighBankShift.program 1613 (bank2.getD · 0) 4 108 ++
    ((leave240.drop 1854).take 16) ++
    HighBankShift.program 1613 (bank3.getD · 0) 8 112 ++
    ((leave240.drop 2206).take 10) ++
    (Leave240Join.digitPass ++ Leave240Join.wordPass) ++
    leave240.drop 2323 := by
  rw [← pass0, ← pass1, ← pass2, ← pass3, ← Leave240Join.emitted]
  simp only [List.append_assoc]
  rw [mergeSlice leave240 2216 107, mergeSlice leave240 2206 10, mergeSlice leave240 1870 336, mergeSlice leave240 1854 16, mergeSlice leave240 1530 324, mergeSlice leave240 1514 16, mergeSlice leave240 1196 318, mergeSlice leave240 1180 16, mergeSlice leave240 865 315, mergeSlice leave240 0 865, List.drop_zero]

end ECDSAAdd.Entrant.StairPacket.Leave240Shift

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

def wordPos (L:SkywalkIntegerLayout) (g:Bool) := if g then L.b else L.a
def wordSigned (L:SkywalkIntegerLayout) (g:Bool) := if g then L.a else L.b
def negative (sg:Bool) (u:Nat) := sg && decide (0<u)

theorem mathematical (L:SkywalkIntegerLayout) (g sg:Bool) (u v:Nat) (s:BasisState)
    (h:SkywalkIntegerInput L (SkywalkRails.encode g sg u v).a (SkywalkRails.encode g sg u v).b g s) :
    let e:=negative sg u
    s L.previous=g ∧ (s L.aSign ^^ s L.bSign)=e ∧
    regValue (wordPos L g) s=u+v ∧
    regValue (wordSigned L g) (fun q=>s q ^^ e)=u-e.toNat := by
  obtain ⟨a,b,g0,_⟩:=h
  have orient (lo:List Wire) (sign:Wire) (signed:signedRegValue (lo++[sign]) s=SkywalkRails.signed sg u) :
      s sign=negative sg u ∧ regValue (lo++[sign]) (fun q=>s q ^^ negative sg u)=u-(negative sg u).toNat := by
    have h:=full lo sign s _ signed
    have n:SkywalkRails.neg (SkywalkRails.signed sg u)=negative sg u := by
      cases sg <;> simp [SkywalkRails.neg,SkywalkRails.signed,negative]
    have r:s sign=negative sg u:=h.1.trans n
    rw [r] at h
    have mag:(SkywalkRails.signed sg u).natAbs=u:=by cases sg <;> simp [SkywalkRails.signed]
    exact ⟨r,by simpa only [mag] using h.2⟩
  cases g with
  | false =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=(u:Int)+v at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=SkywalkRails.signed sg u at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using a)
    obtain ⟨s0,sv⟩:=orient _ _ b
    exact ⟨g0,by rw [p0,s0,Bool.false_xor],pv,sv⟩
  | true =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=SkywalkRails.signed sg u at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=(u:Int)+v at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using b)
    obtain ⟨s0,sv⟩:=orient _ _ a
    exact ⟨g0,by rw [s0,p0,Bool.xor_false],pv,sv⟩

#print axioms mathematical
end ECDSAAdd.Entrant.StairPacket.PortalValues

end












section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem listMap (p:List α) (f g:α→Wire) (s u:BasisState) (same:∀x∈p,s (f x)=u (g x)) :
    regValue (p.map f) s=regValue (p.map g) u := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    change (if s (f x) then 1 else 0)+2*regValue (p.map f) s=(if u (g x) then 1 else 0)+2*regValue (p.map g) u
    rw [same _ (by simp),ih (fun q h=>same q (List.mem_cons_of_mem _ h))]

theorem scan_values (a b g n:Wire) (ps:List (Wire×Wire)) (loc:RailPair.ScanGeometry a b g n ps)
    (s:State) (m:List Bool) (fresh:s.basis n=false) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=s.basis a ^^ s.basis b
    let l:=ps.map Prod.fst; let r:=ps.map Prod.snd
    regValue l t.basis=(if s.basis g then regValue r s.basis else regValue l s.basis) ∧
    regValue r t.basis=(if s.basis g then regValue l (fun q=>s.basis q ^^ e) else regValue r (fun q=>s.basis q ^^ e)) := by
  dsimp only
  have act:=RailPair.scan_run _ _ _ _ _ loc s m fresh
  cases eq:s.basis g <;> simp only [eq,ite_true,Bool.false_eq_true,ite_false] at *
  · exact ⟨listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).1),
      listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).2)⟩
  · exact ⟨listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).1),
      listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).2)⟩

theorem unroute (f:Wire→Wire) (rs:List Wire) (s:BasisState) :
    regValue (rs.map f) s=regValue rs (fun q=>s (f q)) := by
  simpa using listMap rs f id s (fun q=>s (f q)) (fun _ _=>rfl)

end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat

/-- Every shortened decoded state still fits a signed word of log2(U)+3 bits;
the physical sign used by the guard and archive survives numerator reduction. -/
theorem reduced_values (b k : Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let T:=reduced b k z
    let f:=far b k z
    let h:=limb b k
    let d:=if f then gap b k z else 0
    let lu:=decide (f ∧ 2^b≤z.u)
    T.u=z.u-(if lu then d else 0) ∧ (T.u+T.v=z.u+z.v-d) ∧ T.u+T.v<3*h ∧
    PortalValues.negative sg T.u=PortalValues.negative sg z.u ∧
    (T.u-(PortalValues.negative sg T.u).toNat)=
      (z.u-(PortalValues.negative sg z.u).toNat)-(if lu then d else 0) := by
  have hu:0<limb b k:=by simp [limb]
  have half:2^b≤limb b k:=by
    unfold limb;apply Nat.pow_le_pow_right (by decide); omega
  by_cases hf:far b k z
  · obtain ⟨_,lo,hi⟩:=represented b k z small hf
    dsimp only
    rw [reduced,if_pos hf] at lo hi ⊢
    simp only [hf,true_and,ite_true] at *
    by_cases lu:2^b≤z.u
    · simp only [lu,ite_true,decide_true] at lo hi ⊢
      change 2*limb b k≤z.u-gap b k z+z.v at lo
      have hv:z.v<2^b:=by omega
      have nonzero:0<z.u-gap b k z:=by omega
      have nz:0<z.u:=by omega
      simp only [nonzero,nz,PortalValues.negative,decide_true,Bool.and_true]
      exact ⟨trivial,by omega,hi,trivial,by cases sg <;> simp; omega⟩
    · simp only [lu,ite_false,decide_false] at lo hi ⊢
      change 2*limb b k≤z.u+(z.v-gap b k z) at lo
      have nz:0<z.v-gap b k z:=by omega
      exact ⟨rfl,by omega,hi,trivial,rfl⟩
  · have dst:reduced b k z=z:=by simp [reduced,hf]
    have low:(z.u+z.v)/limb b k<3:=Nat.lt_of_not_ge hf
    have lt:z.u+z.v<3*limb b k:=(Nat.div_lt_iff_lt_mul hu).mp low
    simp [dst,hf,lt]
#print axioms reduced_values
end ECDSAAdd.Entrant.StairPacket.Shadow

end


section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Control
open Partial HighBankControl Leave225Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def controls0 : List Wire := [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560]

theorem selection0 (key : Fin 16) :
    parity (fun q => decide (q = Leave225Join.tags.getD key 0)) controls0 = key.val.testBit 0 := by
  revert key
  decide +kernel

theorem away0 : 1613 ∉ controls0 ∧ ∀ q ∈ controls0, q ∉ bank0 := by decide +kernel

theorem on0 : ((leave225.drop 817).take 8) = toggles 1613 controls0 := by rfl
theorem off0 : ((leave225.drop 1116).take 8) = toggles 1613 controls0 := by rfl
theorem reverseOn0 : ((leave225Inv.drop 2068).take 8) = toggles 1613 controls0.reverse := by rfl
theorem reverseOff0 : ((leave225Inv.drop 2367).take 8) = toggles 1613 controls0.reverse := by rfl
theorem wrapped0 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls0)⟩
    let v := run (HighBankShift.program 1613 (bank0.getD · 0) 1 97) m u
    run ((leave225.drop 817).take 307) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave225.drop 817).take 307) =
      toggles 1613 controls0 ++ (HighBankShift.program 1613 (bank0.getD · 0) 1 97 ++ toggles 1613 controls0) := by rfl
  rw [exactSlice]
  apply wrapped layout0 (by decide) _ away0.1
  intro q hq i hi eq
  have h : i < bank0.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away0.2 q hq (eq ▸ List.getElem_mem h)


def controls1 : List Wire := [1563, 1564, 1567, 1568, 1571, 1572, 1575, 1560]

theorem selection1 (key : Fin 16) :
    parity (fun q => decide (q = Leave225Join.tags.getD key 0)) controls1 = key.val.testBit 1 := by
  revert key
  decide +kernel

theorem away1 : 1613 ∉ controls1 ∧ ∀ q ∈ controls1, q ∉ bank1 := by decide +kernel

theorem on1 : ((leave225.drop 1124).take 8) = toggles 1613 controls1 := by rfl
theorem off1 : ((leave225.drop 1426).take 8) = toggles 1613 controls1 := by rfl
theorem reverseOn1 : ((leave225Inv.drop 1758).take 8) = toggles 1613 controls1.reverse := by rfl
theorem reverseOff1 : ((leave225Inv.drop 2060).take 8) = toggles 1613 controls1.reverse := by rfl
theorem wrapped1 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls1)⟩
    let v := run (HighBankShift.program 1613 (bank1.getD · 0) 2 98) m u
    run ((leave225.drop 1124).take 310) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave225.drop 1124).take 310) =
      toggles 1613 controls1 ++ (HighBankShift.program 1613 (bank1.getD · 0) 2 98 ++ toggles 1613 controls1) := by rfl
  rw [exactSlice]
  apply wrapped layout1 (by decide) _ away1.1
  intro q hq i hi eq
  have h : i < bank1.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away1.2 q hq (eq ▸ List.getElem_mem h)


def controls2 : List Wire := [1565, 1566, 1567, 1568, 1573, 1574, 1575, 1560]

theorem selection2 (key : Fin 16) :
    parity (fun q => decide (q = Leave225Join.tags.getD key 0)) controls2 = key.val.testBit 2 := by
  revert key
  decide +kernel

theorem away2 : 1613 ∉ controls2 ∧ ∀ q ∈ controls2, q ∉ bank2 := by decide +kernel

theorem on2 : ((leave225.drop 1434).take 8) = toggles 1613 controls2 := by rfl
theorem off2 : ((leave225.drop 1742).take 8) = toggles 1613 controls2 := by rfl
theorem reverseOn2 : ((leave225Inv.drop 1442).take 8) = toggles 1613 controls2.reverse := by rfl
theorem reverseOff2 : ((leave225Inv.drop 1750).take 8) = toggles 1613 controls2.reverse := by rfl
theorem wrapped2 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls2)⟩
    let v := run (HighBankShift.program 1613 (bank2.getD · 0) 4 100) m u
    run ((leave225.drop 1434).take 316) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave225.drop 1434).take 316) =
      toggles 1613 controls2 ++ (HighBankShift.program 1613 (bank2.getD · 0) 4 100 ++ toggles 1613 controls2) := by rfl
  rw [exactSlice]
  apply wrapped layout2 (by decide) _ away2.1
  intro q hq i hi eq
  have h : i < bank2.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away2.2 q hq (eq ▸ List.getElem_mem h)


def controls3 : List Wire := [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]

theorem selection3 (key : Fin 16) :
    parity (fun q => decide (q = Leave225Join.tags.getD key 0)) controls3 = key.val.testBit 3 := by
  revert key
  decide +kernel

theorem away3 : 1613 ∉ controls3 ∧ ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel

theorem on3 : ((leave225.drop 1750).take 8) = toggles 1613 controls3 := by rfl
theorem off3 : ((leave225.drop 2070).take 8) = toggles 1613 controls3 := by rfl
theorem reverseOn3 : ((leave225Inv.drop 1114).take 8) = toggles 1613 controls3.reverse := by rfl
theorem reverseOff3 : ((leave225Inv.drop 1434).take 8) = toggles 1613 controls3.reverse := by rfl
theorem wrapped3 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls3)⟩
    let v := run (HighBankShift.program 1613 (bank3.getD · 0) 8 104) m u
    run ((leave225.drop 1750).take 328) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave225.drop 1750).take 328) =
      toggles 1613 controls3 ++ (HighBankShift.program 1613 (bank3.getD · 0) 8 104 ++ toggles 1613 controls3) := by rfl
  rw [exactSlice]
  apply wrapped layout3 (by decide) _ away3.1
  intro q hq i hi eq
  have h : i < bank3.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away3.2 q hq (eq ▸ List.getElem_mem h)


end ECDSAAdd.Entrant.StairPacket.Leave225Control

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Control
open Partial HighBankControl Leave240Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def controls0 : List Wire := [1562, 1564, 1566, 1568, 1570, 1572, 1574, 1560]

theorem selection0 (key : Fin 16) :
    parity (fun q => decide (q = Leave240Join.tags.getD key 0)) controls0 = key.val.testBit 0 := by
  revert key
  decide +kernel

theorem away0 : 1613 ∉ controls0 ∧ ∀ q ∈ controls0, q ∉ bank0 := by decide +kernel

theorem on0 : ((leave240.drop 857).take 8) = toggles 1613 controls0 := by rfl
theorem off0 : ((leave240.drop 1180).take 8) = toggles 1613 controls0 := by rfl
theorem reverseOn0 : ((leave240Inv.drop 2202).take 8) = toggles 1613 controls0.reverse := by rfl
theorem reverseOff0 : ((leave240Inv.drop 2525).take 8) = toggles 1613 controls0.reverse := by rfl
theorem wrapped0 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls0)⟩
    let v := run (HighBankShift.program 1613 (bank0.getD · 0) 1 105) m u
    run ((leave240.drop 857).take 331) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave240.drop 857).take 331) =
      toggles 1613 controls0 ++ (HighBankShift.program 1613 (bank0.getD · 0) 1 105 ++ toggles 1613 controls0) := by rfl
  rw [exactSlice]
  apply wrapped layout0 (by decide) _ away0.1
  intro q hq i hi eq
  have h : i < bank0.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away0.2 q hq (eq ▸ List.getElem_mem h)


def controls1 : List Wire := [1563, 1564, 1567, 1568, 1571, 1572, 1575, 1560]

theorem selection1 (key : Fin 16) :
    parity (fun q => decide (q = Leave240Join.tags.getD key 0)) controls1 = key.val.testBit 1 := by
  revert key
  decide +kernel

theorem away1 : 1613 ∉ controls1 ∧ ∀ q ∈ controls1, q ∉ bank1 := by decide +kernel

theorem on1 : ((leave240.drop 1188).take 8) = toggles 1613 controls1 := by rfl
theorem off1 : ((leave240.drop 1514).take 8) = toggles 1613 controls1 := by rfl
theorem reverseOn1 : ((leave240Inv.drop 1868).take 8) = toggles 1613 controls1.reverse := by rfl
theorem reverseOff1 : ((leave240Inv.drop 2194).take 8) = toggles 1613 controls1.reverse := by rfl
theorem wrapped1 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls1)⟩
    let v := run (HighBankShift.program 1613 (bank1.getD · 0) 2 106) m u
    run ((leave240.drop 1188).take 334) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave240.drop 1188).take 334) =
      toggles 1613 controls1 ++ (HighBankShift.program 1613 (bank1.getD · 0) 2 106 ++ toggles 1613 controls1) := by rfl
  rw [exactSlice]
  apply wrapped layout1 (by decide) _ away1.1
  intro q hq i hi eq
  have h : i < bank1.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away1.2 q hq (eq ▸ List.getElem_mem h)


def controls2 : List Wire := [1565, 1566, 1567, 1568, 1573, 1574, 1575, 1560]

theorem selection2 (key : Fin 16) :
    parity (fun q => decide (q = Leave240Join.tags.getD key 0)) controls2 = key.val.testBit 2 := by
  revert key
  decide +kernel

theorem away2 : 1613 ∉ controls2 ∧ ∀ q ∈ controls2, q ∉ bank2 := by decide +kernel

theorem on2 : ((leave240.drop 1522).take 8) = toggles 1613 controls2 := by rfl
theorem off2 : ((leave240.drop 1854).take 8) = toggles 1613 controls2 := by rfl
theorem reverseOn2 : ((leave240Inv.drop 1528).take 8) = toggles 1613 controls2.reverse := by rfl
theorem reverseOff2 : ((leave240Inv.drop 1860).take 8) = toggles 1613 controls2.reverse := by rfl
theorem wrapped2 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls2)⟩
    let v := run (HighBankShift.program 1613 (bank2.getD · 0) 4 108) m u
    run ((leave240.drop 1522).take 340) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave240.drop 1522).take 340) =
      toggles 1613 controls2 ++ (HighBankShift.program 1613 (bank2.getD · 0) 4 108 ++ toggles 1613 controls2) := by rfl
  rw [exactSlice]
  apply wrapped layout2 (by decide) _ away2.1
  intro q hq i hi eq
  have h : i < bank2.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away2.2 q hq (eq ▸ List.getElem_mem h)


def controls3 : List Wire := [1569, 1570, 1571, 1572, 1573, 1574, 1575, 1560]

theorem selection3 (key : Fin 16) :
    parity (fun q => decide (q = Leave240Join.tags.getD key 0)) controls3 = key.val.testBit 3 := by
  revert key
  decide +kernel

theorem away3 : 1613 ∉ controls3 ∧ ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel

theorem on3 : ((leave240.drop 1862).take 8) = toggles 1613 controls3 := by rfl
theorem off3 : ((leave240.drop 2206).take 8) = toggles 1613 controls3 := by rfl
theorem reverseOn3 : ((leave240Inv.drop 1176).take 8) = toggles 1613 controls3.reverse := by rfl
theorem reverseOff3 : ((leave240Inv.drop 1520).take 8) = toggles 1613 controls3.reverse := by rfl
theorem wrapped3 (s : State) (m : List Bool) :
    let u : State := ⟨s.phase,writeBit s.basis 1613 (s.basis 1613 ^^ parity s.basis controls3)⟩
    let v := run (HighBankShift.program 1613 (bank3.getD · 0) 8 112) m u
    run ((leave240.drop 1862).take 352) m s = ⟨v.phase,writeBit v.basis 1613 (s.basis 1613)⟩ := by
  have exactSlice : ((leave240.drop 1862).take 352) =
      toggles 1613 controls3 ++ (HighBankShift.program 1613 (bank3.getD · 0) 8 112 ++ toggles 1613 controls3) := by rfl
  rw [exactSlice]
  apply wrapped layout3 (by decide) _ away3.1
  intro q hq i hi eq
  have h : i < bank3.length := hi
  rw [List.getD_eq_getElem _ _ h] at eq
  exact away3.2 q hq (eq ▸ List.getElem_mem h)


end ECDSAAdd.Entrant.StairPacket.Leave240Control

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Partial LeaveSelector HighBankFirstHit Leave255Hit
set_option maxRecDepth 50000

def far : List Op := [.xor 1559 1710, .xor 1561 1710, .xor 1562 1710, .xor 1563 1710, .xor 1564 1710, .xor 1565 1710]
def zero : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffix : List Op := [.save 284 285 1577, .save 283 1577 1578, .save 282 1578 1579, .save 281 1579 1580, .save 280 1580 1581, .save 279 1581 1582, .save 278 1582 1583, .save 277 1583 1584, .save 276 1584 1585, .save 275 1585 1586, .save 274 1586 1587, .save 273 1587 1588]
def select : List Op := [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593, .save 1567 1578 1594, .save 1568 285 1595]
def cross : List Op := [.mix 1576 416 1709, .mix 1562 417 1709, .mix 1563 418 1709, .mix 1564 419 1709, .mix 1565 420 1709, .mix 1566 421 1709, .mix 1567 422 1709, .mix 1568 423 1709, .mix 1569 424 1709, .mix 1570 425 1709, .mix 1571 426 1709, .mix 1572 427 1709, .mix 1573 428 1709, .mix 1574 429 1709, .mix 1575 430 1709, .mix 1560 431 1709]
def sign : List Op := [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596, .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596, .xor 1560 1596]
def product : List Op := [.save 1709 1596 1597]

def prepare := far ++ zero ++ suffix ++ select ++ cross ++ sign ++ product
def retire := (product.reverse ++ sign ++ select.reverse ++ suffix.reverse ++ zero)
def prepareInv := zero.reverse ++ suffix ++ select ++ sign.reverse ++ product
def retireInv := prepare.reverse

theorem prepared : ((leave255.drop 275).take 59) = prepare.map Op.enter := by rfl

theorem retired : ((leave255.drop 2445).take 37) = retire.map Op.exit := by rfl

theorem preparedInv : ((leave255Inv.drop 1028).take 37) = prepareInv.map Op.enter := by rfl

theorem retiredInv : ((leave255Inv.drop 3176).take 59) = retireInv.map Op.exit := by rfl

theorem hitsInv : ((leave255Inv.drop 998).take 30) = putAll 1560 swaps hits 0 15 := by rfl

theorem retireHits : ((leave255.drop 2482).take 30) = dropAll 1560 swaps hits 0 15 := by rfl

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem third (a b c:Wire) (rest:List Wire) (s:BasisState) :
    s c=true ↔ 4≤regValue (a::b::c::rest) s%8 := by
  change s c=true ↔ 4≤((if s a then 1 else 0)+2*((if s b then 1 else 0)+
      2*((if s c then 1 else 0)+2*regValue rest s)))%8
  cases s a <;> cases s b <;> cases s c <;> simp <;> omega

theorem wideThird (a b c:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (hp:0<U) (eq:regValue (a::b::c::rest) s=W/U) :
    s c=true ↔ 4*U≤W%(8*U) := by
  rw [third a b c rest s,eq,Nat.mul_comm 8 U,Nat.mod_mul]
  have rem:=Nat.mod_lt W hp
  constructor
  · intro h
    have big:=Nat.mul_le_mul_left U h
    omega
  · intro h
    by_contra not
    have ub:(W/U%8)+1≤4:=by omega
    have p:=Nat.mul_le_mul_left U ub
    rw [Nat.mul_add,Nat.mul_one] at p
    omega

theorem upper (a b c:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (eq:regValue (a::b::c::rest) s=W/U) :
    regValue rest s=W/(8*U) := by
  have z:=shiftedValue (a::b::c::rest) 3 (by simp) s
  rw [eq,Nat.div_div_eq_div_mul,Nat.mul_comm U] at z
  exact z

theorem input_eq (a0 a1 a2 b0 b1 b2 long:Wire) (xs ys:List Wire) (s:BasisState)
    (U small u v e:Nat) (unit:2*small≤U) (bp:0<small) (sz:min u v<small) (en:e≤1) (eu:e≤u)
    (a:regValue (a0::a1::a2::xs) s=(u+v)/U)
    (b:regValue (b0::b1::b2::ys) s=(u-e)/U)
    (orient:s long=decide (3*U≤u+v ∧ small≤u)) (same:xs.length=ys.length) :
    (regValue ys s+(s b2 && !s a2).toNat)%2^ys.length=copyValue (some long) s (regValue xs s) := by
  have hp:0<U:=by omega
  have ax:=wideThird _ _ _ _ _ U _ hp a
  have by':=wideThird _ _ _ _ _ U _ hp b
  have bits:(s b2 && !s a2).toNat =
      if 4*U≤(u-e)%(8*U) ∧ (u+v)%(8*U)<4*U then 1 else 0 := by
    cases bbit:s b2 <;> cases abit:s a2 <;> simp_all
  have v':=PortalCut.clear_value small U u v e unit bp sz en eu
  rw [upper _ _ _ _ _ U _ b,bits,v',copyValue,orient,upper _ _ _ _ _ U _ a]
  by_cases cond:3*U≤u+v ∧ small≤u
  · simp only [cond]
    apply Nat.mod_eq_of_lt
    rw [←upper _ _ _ _ _ U _ a,←same]
    exact regValue_lt _ _
  · simp [cond]
#print axioms input_eq
end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Barrel
open Partial Leave225Control Leave225Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev wire (i : Nat) := bank3.getD i 0
def passes0 : Program := []
def passes1 := passes0 ++ stage 1613 wire controls0 1 97
def passes2 := passes1 ++ stage 1613 wire controls1 2 98
def passes3 := passes2 ++ stage 1613 wire controls2 4 100
def passes4 := passes3 ++ stage 1613 wire controls3 8 104

theorem emitted : ((leave225.drop 817).take 1261) = passes4 := by rfl

theorem value (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^97) (h : holds wire 112 x s) (clean : s.basis 1613=false)
    (tags : ∀ q ∈ Leave225Join.tags, s.basis q = decide (q = Leave225Join.tags.getD key 0)) :
    Result wire 112 (x <<< key.val) s (run ((leave225.drop 817).take 1261) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 112 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 112 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 97+0 ≤ 97)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls0, q ∈ Leave225Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 112 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 97+(key.val % 2) ≤ 98)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls1, q ∈ Leave225Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 112 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 97+(key.val % 4) ≤ 100)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls2, q ∈ Leave225Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 112 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 97+(key.val % 8) ≤ 104)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls3, q ∈ Leave225Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave225Barrel

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Barrel
open Partial Leave240Control Leave240Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev wire (i : Nat) := bank3.getD i 0
def passes0 : Program := []
def passes1 := passes0 ++ stage 1613 wire controls0 1 105
def passes2 := passes1 ++ stage 1613 wire controls1 2 106
def passes3 := passes2 ++ stage 1613 wire controls2 4 108
def passes4 := passes3 ++ stage 1613 wire controls3 8 112

theorem emitted : ((leave240.drop 857).take 1357) = passes4 := by rfl

theorem value (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^105) (h : holds wire 120 x s) (clean : s.basis 1613=false)
    (tags : ∀ q ∈ Leave240Join.tags, s.basis q = decide (q = Leave240Join.tags.getD key 0)) :
    Result wire 120 (x <<< key.val) s (run ((leave240.drop 857).take 1357) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 120 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 120 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 105+0 ≤ 105)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls0, q ∈ Leave240Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 120 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 105+(key.val % 2) ≤ 106)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls1, q ∈ Leave240Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 120 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 105+(key.val % 4) ≤ 108)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls2, q ∈ Leave240Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 120 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 105+(key.val % 8) ≤ 112)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · have sub : ∀ q ∈ controls3, q ∈ Leave240Join.tags := by decide +kernel
      rw [parity_congr (fun q hq => tags q (sub q hq)), selection3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave240Barrel

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
def longPairs : List (Wire × Wire) := [(931,1557),(932,1558),(933,1559),(934,1560),(935,1561),(936,1562),(937,1563),(938,1564),(939,1565),(940,1566),(941,1567),(942,1568),(943,1569),(944,1570),(945,1571),(946,1572),(947,1573),(948,1574)]
theorem long_layout : (1556::930::sites longPairs).Nodup := by decide +kernel
def long : Program := ((Partial.leave225).drop 93).take 76
theorem long_eq : long = latch true none 1556 930 longPairs := by decide +kernel
def longBack : Program := ((Partial.leave225Inv).drop 3023).take 76
theorem longBack_eq : longBack = backwardLatch true none 1556 930 longPairs := by decide +kernel
theorem long_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run long m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 930 longPairs).any s.basis))⟩ := by
  rw [long_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 930 longPairs long_layout (by simp) s m clean
theorem longBack_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run longBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 930 longPairs).any s.basis))⟩ := by
  rw [longBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 930 longPairs long_layout (by simp) s m clean
def pendingPairs : List (Wire × Wire) := [(410,1559),(956,1560),(957,1561),(958,1562),(959,1563),(960,1564),(961,1565),(962,1566),(963,1567),(964,1568),(965,1569),(966,1570),(967,1571),(968,1572),(969,1573),(970,1574),(971,1575),(972,1576),(973,1577),(974,1578),(975,1579),(976,1580),(977,1581),(978,1582),(979,1583),(980,1584),(981,1585),(982,1586),(983,1587),(984,1588),(985,1589),(986,1590),(987,1591),(988,1592),(989,1593),(990,1594),(991,1595),(992,1596),(993,1597),(994,1613),(995,1614),(996,1615),(997,1616),(998,1617),(999,1618),(1000,1619),(1001,1620),(1002,1621),(1003,1622),(1004,1623),(1005,1624),(1006,1625),(1007,1626),(1008,1627),(1009,1628),(1010,1629),(1011,1630),(1012,1631),(1013,1632),(1014,1633),(1015,1634),(1016,1635),(1017,1636),(1018,1637),(1019,1638),(1020,1639),(1021,1640),(1022,1641),(1023,1642),(1024,1643),(1025,1644),(1026,1645),(1027,1646),(1028,1647),(1029,1648),(1030,1649),(1031,1650),(1032,1651),(1033,1652),(1034,1653),(1035,1654),(1036,1655),(1037,1656),(1038,1657),(1039,1658),(1040,1659),(1041,1660),(1042,1661),(1598,1662),(1599,1663),(1600,1664),(1601,1665),(1602,1666),(1603,1667),(1604,1668),(1605,1669),(1606,1670),(1607,1671),(1608,1672),(1609,1673),(1610,1674),(1611,1675),(1612,1676)]
theorem pending_layout : (408::409::1557::1558::sites pendingPairs).Nodup := by decide +kernel
def pending : Program := ((Partial.leave225).drop 2321).take 418
theorem pending_eq : pending = threshold 408 409 1558 1557 pendingPairs := by decide +kernel
def pendingBack : Program := ((Partial.leave225Inv).drop 453).take 418
theorem pendingBack_eq : pendingBack = thresholdBack 408 409 1558 1557 pendingPairs := by decide +kernel
theorem pending_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 408 409 pendingPairs s.basis))⟩ := by
  rw [pending_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_run 408 409 1558 1557 pendingPairs pending_layout s m fresh clean
theorem pendingBack_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 408 409 pendingPairs s.basis))⟩ := by
  rw [pendingBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_back 408 409 1558 1557 pendingPairs pending_layout s m fresh clean
def clearFlagPairs : List (Wire × Wire) := [(930,1559),(931,1560),(932,1561),(933,1562),(934,1563),(935,1564),(936,1565),(937,1566),(938,1567),(939,1568),(940,1569)]
theorem clearFlag_layout : (1556::1558::sites clearFlagPairs).Nodup := by decide +kernel
def clearFlag : Program := ((Partial.leave225).drop 2740).take 48
theorem clearFlag_eq : clearFlag = latch true none 1556 1558 clearFlagPairs := by decide +kernel
def clearFlagBack : Program := ((Partial.leave225Inv).drop 404).take 48
theorem clearFlagBack_eq : clearFlagBack = backwardLatch true none 1556 1558 clearFlagPairs := by decide +kernel
theorem clearFlag_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlag m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlag_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
theorem clearFlagBack_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlagBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlagBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
def fullA : List Wire := [401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418]
def fullM : List Wire := [931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948]
def fullC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575]
theorem full_geometry : Companion.Geometry fullA fullM fullC 1556 1558 := by
  constructor <;> decide +kernel
def smallA : List Wire := [401,402,403,404,405,406,407,408,409,410]
def smallM : List Wire := [931,932,933,934,935,936,937,938,939,940]
def smallC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567]
theorem small_geometry : Companion.Geometry smallA smallM smallC 1556 1558 := by
  constructor <;> decide +kernel
def erase : Program := ((Partial.leave225).drop 172).take 70
theorem erase_eq : erase = Companion.erase fullA fullM fullC 1556 1558 := by decide +kernel
def eraseBack : Program := ((Partial.leave225Inv).drop 2950).take 70
theorem eraseBack_eq : eraseBack = PortalBorrow.restore fullA fullM fullC 1556 1558 := by decide +kernel
def restore : Program := ((Partial.leave225).drop 2260).take 58
theorem restore_eq : restore = Companion.restore smallA smallM smallC 1556 1558 := by decide +kernel
def restoreBack : Program := ((Partial.leave225Inv).drop 874).take 58
theorem restoreBack_eq : restoreBack = (notRegister smallM).reverse ++ PortalUnitInverse.emit smallM smallC 1558 ++ (notRegister smallM).reverse ++ (copyRegister (some 1556) smallA smallM).reverse := by decide +kernel
def mask : Program := ((Partial.leave225).drop 169).take 3
theorem mask_eq : mask = ([.X 1557,.CX 400 1557,.CCX 930 1557 1558]:Program) := by decide +kernel
def maskBack : Program := ((Partial.leave225Inv).drop 3020).take 3
theorem maskBack_eq : maskBack = ([.measureX 1558 [] [.CZ 930 1557],.CX 400 1557,.X 1557]:Program) := by decide +kernel
def releaseMask : Program := ((Partial.leave225).drop 2318).take 3
theorem releaseMask_eq : releaseMask = ([.measureX 1558 [] [.CZ 930 1557],.CX 400 1557,.X 1557]:Program) := by decide +kernel
def releaseMaskBack : Program := ((Partial.leave225Inv).drop 871).take 3
theorem releaseMaskBack_eq : releaseMaskBack = ([.X 1557,.CX 400 1557,.CCX 930 1557 1558]:Program) := by decide +kernel
def nextU : Program := ((Partial.leave225).drop 2739).take 1
theorem nextU_eq : nextU = ([.CCX 1556 1557 1558]:Program) := by decide +kernel
def nextUBack : Program := ((Partial.leave225Inv).drop 452).take 1
theorem nextUBack_eq : nextUBack = ([.measureX 1558 [] [.CZ 1556 1557]]:Program) := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
def longPairs : List (Wire × Wire) := [(923,1557),(924,1558),(925,1559),(926,1560),(927,1561),(928,1562),(929,1563),(930,1564),(931,1565),(932,1566),(933,1567),(934,1568),(935,1569),(936,1570),(937,1571),(938,1572),(939,1573),(940,1574)]
theorem long_layout : (1556::922::sites longPairs).Nodup := by decide +kernel
def long : Program := ((Partial.leave240).drop 93).take 76
theorem long_eq : long = latch true none 1556 922 longPairs := by decide +kernel
def longBack : Program := ((Partial.leave240Inv).drop 3221).take 76
theorem longBack_eq : longBack = backwardLatch true none 1556 922 longPairs := by decide +kernel
theorem long_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run long m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 922 longPairs).any s.basis))⟩ := by
  rw [long_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 922 longPairs long_layout (by simp) s m clean
theorem longBack_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run longBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 922 longPairs).any s.basis))⟩ := by
  rw [longBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 922 longPairs long_layout (by simp) s m clean
def pendingPairs : List (Wire × Wire) := [(418,1559),(949,1560),(950,1561),(951,1562),(952,1563),(953,1564),(954,1565),(955,1566),(956,1567),(957,1568),(958,1569),(959,1570),(960,1571),(961,1572),(962,1573),(963,1574),(964,1575),(965,1576),(966,1577),(967,1578),(968,1579),(969,1580),(970,1581),(971,1582),(972,1583),(973,1584),(974,1585),(975,1586),(976,1587),(977,1588),(978,1589),(979,1590),(980,1591),(981,1592),(982,1593),(983,1594),(984,1595),(985,1596),(986,1597),(987,1613),(988,1614),(989,1615),(990,1616),(991,1617),(992,1618),(993,1619),(994,1620),(995,1621),(996,1622),(997,1623),(998,1624),(999,1625),(1000,1626),(1001,1627),(1002,1628),(1003,1629),(1004,1630),(1005,1631),(1006,1632),(1007,1633),(1008,1634),(1009,1635),(1010,1636),(1011,1637),(1012,1638),(1013,1639),(1014,1640),(1015,1641),(1016,1642),(1017,1643),(1018,1644),(1019,1645),(1020,1646),(1021,1647),(1022,1648),(1023,1649),(1024,1650),(1025,1651),(1026,1652),(1027,1653),(1028,1654),(1029,1655),(1030,1656),(1031,1657),(1032,1658),(1033,1659),(1034,1660),(1035,1661),(1036,1662),(1037,1663),(1038,1664),(1039,1665),(1040,1666),(1041,1667),(1042,1668),(1598,1669),(1599,1670),(1600,1671),(1601,1672),(1602,1673),(1603,1674),(1604,1675),(1605,1676),(1606,1677),(1607,1678),(1608,1679),(1609,1680),(1610,1681),(1611,1682),(1612,1683)]
theorem pending_layout : (416::417::1557::1558::sites pendingPairs).Nodup := by decide +kernel
def pending : Program := ((Partial.leave240).drop 2462).take 446
theorem pending_eq : pending = threshold 416 417 1558 1557 pendingPairs := by decide +kernel
def pendingBack : Program := ((Partial.leave240Inv).drop 482).take 446
theorem pendingBack_eq : pendingBack = thresholdBack 416 417 1558 1557 pendingPairs := by decide +kernel
theorem pending_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 416 417 pendingPairs s.basis))⟩ := by
  rw [pending_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_run 416 417 1558 1557 pendingPairs pending_layout s m fresh clean
theorem pendingBack_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 416 417 pendingPairs s.basis))⟩ := by
  rw [pendingBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_back 416 417 1558 1557 pendingPairs pending_layout s m fresh clean
def clearFlagPairs : List (Wire × Wire) := [(922,1559),(923,1560),(924,1561),(925,1562),(926,1563),(927,1564),(928,1565),(929,1566),(930,1567),(931,1568),(932,1569),(933,1570)]
theorem clearFlag_layout : (1556::1558::sites clearFlagPairs).Nodup := by decide +kernel
def clearFlag : Program := ((Partial.leave240).drop 2909).take 52
theorem clearFlag_eq : clearFlag = latch true none 1556 1558 clearFlagPairs := by decide +kernel
def clearFlagBack : Program := ((Partial.leave240Inv).drop 429).take 52
theorem clearFlagBack_eq : clearFlagBack = backwardLatch true none 1556 1558 clearFlagPairs := by decide +kernel
theorem clearFlag_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlag m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlag_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
theorem clearFlagBack_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlagBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlagBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
def fullA : List Wire := [408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425]
def fullM : List Wire := [923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940]
def fullC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575]
theorem full_geometry : Companion.Geometry fullA fullM fullC 1556 1558 := by
  constructor <;> decide +kernel
def smallA : List Wire := [408,409,410,411,412,413,414,415,416,417,418]
def smallM : List Wire := [923,924,925,926,927,928,929,930,931,932,933]
def smallC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568]
theorem small_geometry : Companion.Geometry smallA smallM smallC 1556 1558 := by
  constructor <;> decide +kernel
def erase : Program := ((Partial.leave240).drop 172).take 70
theorem erase_eq : erase = Companion.erase fullA fullM fullC 1556 1558 := by decide +kernel
def eraseBack : Program := ((Partial.leave240Inv).drop 3148).take 70
theorem eraseBack_eq : eraseBack = PortalBorrow.restore fullA fullM fullC 1556 1558 := by decide +kernel
def restore : Program := ((Partial.leave240).drop 2395).take 64
theorem restore_eq : restore = Companion.restore smallA smallM smallC 1556 1558 := by decide +kernel
def restoreBack : Program := ((Partial.leave240Inv).drop 931).take 64
theorem restoreBack_eq : restoreBack = (notRegister smallM).reverse ++ PortalUnitInverse.emit smallM smallC 1558 ++ (notRegister smallM).reverse ++ (copyRegister (some 1556) smallA smallM).reverse := by decide +kernel
def mask : Program := ((Partial.leave240).drop 169).take 3
theorem mask_eq : mask = ([.X 1557,.CX 407 1557,.CCX 922 1557 1558]:Program) := by decide +kernel
def maskBack : Program := ((Partial.leave240Inv).drop 3218).take 3
theorem maskBack_eq : maskBack = ([.measureX 1558 [] [.CZ 922 1557],.CX 407 1557,.X 1557]:Program) := by decide +kernel
def releaseMask : Program := ((Partial.leave240).drop 2459).take 3
theorem releaseMask_eq : releaseMask = ([.measureX 1558 [] [.CZ 922 1557],.CX 407 1557,.X 1557]:Program) := by decide +kernel
def releaseMaskBack : Program := ((Partial.leave240Inv).drop 928).take 3
theorem releaseMaskBack_eq : releaseMaskBack = ([.X 1557,.CX 407 1557,.CCX 922 1557 1558]:Program) := by decide +kernel
def nextU : Program := ((Partial.leave240).drop 2908).take 1
theorem nextU_eq : nextU = ([.CCX 1556 1557 1558]:Program) := by decide +kernel
def nextUBack : Program := ((Partial.leave240Inv).drop 481).take 1
theorem nextUBack_eq : nextUBack = ([.measureX 1558 [] [.CZ 1556 1557]]:Program) := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
def longPairs : List (Wire × Wire) := [(916,1557),(917,1558),(918,1559),(919,1560),(920,1561),(921,1562),(922,1563),(923,1564),(924,1565),(925,1566),(926,1567),(927,1568),(928,1569),(929,1570),(930,1571),(931,1572),(932,1573),(933,1574)]
theorem long_layout : (1556::915::sites longPairs).Nodup := by decide +kernel
def long : Program := ((Partial.leave255).drop 93).take 76
theorem long_eq : long = latch true none 1556 915 longPairs := by decide +kernel
def longBack : Program := ((Partial.leave255Inv).drop 3341).take 76
theorem longBack_eq : longBack = backwardLatch true none 1556 915 longPairs := by decide +kernel
theorem long_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run long m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 915 longPairs).any s.basis))⟩ := by
  rw [long_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 915 longPairs long_layout (by simp) s m clean
theorem longBack_run (s:State) (m:List Bool) (clean:∀p∈longPairs,s.basis p.2=false) :
    run longBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 915 longPairs).any s.basis))⟩ := by
  rw [longBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 915 longPairs long_layout (by simp) s m clean
def pendingPairs : List (Wire × Wire) := [(425,1559),(941,1560),(942,1561),(943,1562),(944,1563),(945,1564),(946,1565),(947,1566),(948,1567),(949,1568),(950,1569),(951,1570),(952,1571),(953,1572),(954,1573),(955,1574),(956,1575),(957,1576),(958,1577),(959,1578),(960,1579),(961,1580),(962,1581),(963,1582),(964,1583),(965,1584),(966,1585),(967,1586),(968,1587),(969,1588),(970,1589),(971,1590),(972,1591),(973,1592),(974,1593),(975,1594),(976,1595),(977,1596),(978,1597),(979,1613),(980,1614),(981,1615),(982,1616),(983,1617),(984,1618),(985,1619),(986,1620),(987,1621),(988,1622),(989,1623),(990,1624),(991,1625),(992,1626),(993,1627),(994,1628),(995,1629),(996,1630),(997,1631),(998,1632),(999,1633),(1000,1634),(1001,1635),(1002,1636),(1003,1637),(1004,1638),(1005,1639),(1006,1640),(1007,1641),(1008,1642),(1009,1643),(1010,1644),(1011,1645),(1012,1646),(1013,1647),(1014,1648),(1015,1649),(1016,1650),(1017,1651),(1018,1652),(1019,1653),(1020,1654),(1021,1655),(1022,1656),(1023,1657),(1024,1658),(1025,1659),(1026,1660),(1027,1661),(1028,1662),(1029,1663),(1030,1664),(1031,1665),(1032,1666),(1033,1667),(1034,1668),(1035,1669),(1036,1670),(1037,1671),(1038,1672),(1039,1673),(1040,1674),(1041,1675),(1042,1676),(1598,1677),(1599,1678),(1600,1679),(1601,1680),(1602,1681),(1603,1682),(1604,1683),(1605,1684),(1606,1685),(1607,1686),(1608,1687),(1609,1688),(1610,1689),(1611,1690),(1612,1691)]
theorem pending_layout : (423::424::1557::1558::sites pendingPairs).Nodup := by decide +kernel
def pending : Program := ((Partial.leave255).drop 2576).take 478
theorem pending_eq : pending = threshold 423 424 1558 1557 pendingPairs := by decide +kernel
def pendingBack : Program := ((Partial.leave255Inv).drop 456).take 478
theorem pendingBack_eq : pendingBack = thresholdBack 423 424 1558 1557 pendingPairs := by decide +kernel
theorem pending_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 423 424 pendingPairs s.basis))⟩ := by
  rw [pending_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_run 423 424 1558 1557 pendingPairs pending_layout s m fresh clean
theorem pendingBack_run (s:State) (m:List Bool) (fresh : s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s = ⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ (high 423 424 pendingPairs s.basis))⟩ := by
  rw [pendingBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using threshold_back 423 424 1558 1557 pendingPairs pending_layout s m fresh clean
def clearFlagPairs : List (Wire × Wire) := [(915,1559),(916,1560),(917,1561),(918,1562),(919,1563),(920,1564),(921,1565),(922,1566),(923,1567),(924,1568),(925,1569)]
theorem clearFlag_layout : (1556::1558::sites clearFlagPairs).Nodup := by decide +kernel
def clearFlag : Program := ((Partial.leave255).drop 3055).take 48
theorem clearFlag_eq : clearFlag = latch true none 1556 1558 clearFlagPairs := by decide +kernel
def clearFlagBack : Program := ((Partial.leave255Inv).drop 407).take 48
theorem clearFlagBack_eq : clearFlagBack = backwardLatch true none 1556 1558 clearFlagPairs := by decide +kernel
theorem clearFlag_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlag m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlag_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using run_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
theorem clearFlagBack_run (s:State) (m:List Bool) (clean:∀p∈clearFlagPairs,s.basis p.2=false) :
    run clearFlagBack m s = ⟨s.phase,writeBit s.basis 1556 (s.basis 1556 ^^ ((digits 1558 clearFlagPairs).any s.basis))⟩ := by
  rw [clearFlagBack_eq]
  simpa only [active,Option.elim_none,Bool.true_and,high] using backward_latch true none 1556 1558 clearFlagPairs clearFlag_layout (by simp) s m clean
def fullA : List Wire := [416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433]
def fullM : List Wire := [916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933]
def fullC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575]
theorem full_geometry : Companion.Geometry fullA fullM fullC 1556 1558 := by
  constructor <;> decide +kernel
def smallA : List Wire := [416,417,418,419,420,421,422,423,424,425]
def smallM : List Wire := [916,917,918,919,920,921,922,923,924,925]
def smallC : List Wire := [1559,1560,1561,1562,1563,1564,1565,1566,1567]
theorem small_geometry : Companion.Geometry smallA smallM smallC 1556 1558 := by
  constructor <;> decide +kernel
def erase : Program := ((Partial.leave255).drop 172).take 70
theorem erase_eq : erase = Companion.erase fullA fullM fullC 1556 1558 := by decide +kernel
def eraseBack : Program := ((Partial.leave255Inv).drop 3268).take 70
theorem eraseBack_eq : eraseBack = PortalBorrow.restore fullA fullM fullC 1556 1558 := by decide +kernel
def restore : Program := ((Partial.leave255).drop 2515).take 58
theorem restore_eq : restore = Companion.restore smallA smallM smallC 1556 1558 := by decide +kernel
def restoreBack : Program := ((Partial.leave255Inv).drop 937).take 58
theorem restoreBack_eq : restoreBack = (notRegister smallM).reverse ++ PortalUnitInverse.emit smallM smallC 1558 ++ (notRegister smallM).reverse ++ (copyRegister (some 1556) smallA smallM).reverse := by decide +kernel
def mask : Program := ((Partial.leave255).drop 169).take 3
theorem mask_eq : mask = ([.X 1557,.CX 415 1557,.CCX 915 1557 1558]:Program) := by decide +kernel
def maskBack : Program := ((Partial.leave255Inv).drop 3338).take 3
theorem maskBack_eq : maskBack = ([.measureX 1558 [] [.CZ 915 1557],.CX 415 1557,.X 1557]:Program) := by decide +kernel
def releaseMask : Program := ((Partial.leave255).drop 2573).take 3
theorem releaseMask_eq : releaseMask = ([.measureX 1558 [] [.CZ 915 1557],.CX 415 1557,.X 1557]:Program) := by decide +kernel
def releaseMaskBack : Program := ((Partial.leave255Inv).drop 934).take 3
theorem releaseMaskBack_eq : releaseMaskBack = ([.X 1557,.CX 415 1557,.CCX 915 1557 1558]:Program) := by decide +kernel
def nextU : Program := ((Partial.leave255).drop 3054).take 1
theorem nextU_eq : nextU = ([.CCX 1556 1557 1558]:Program) := by decide +kernel
def nextUBack : Program := ((Partial.leave255Inv).drop 455).take 1
theorem nextUBack_eq : nextUBack = ([.measureX 1558 [] [.CZ 1556 1557]]:Program) := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

theorem erase_undo (A M C : List Wire) (long borrow : Wire)
    (L : Companion.Geometry A M C long borrow)
    (proper : ProperProgram (copyRegister (some long) A M)) (s : State) (m n : List Bool)
    (clean : ∀ q ∈ C, s.basis q = false) :
    run (PortalBorrow.restore A M C long borrow) n (run (Companion.erase A M C long borrow) m s) = s := by
  simp only [PortalBorrow.restore, Companion.erase, run_append, run_take]
  rw [run_reverse_proper _ proper]
  exact PortalUnitInverse.undo M C borrow L.carries L.ripple _ _ _ clean

def restoreBack (A M C : List Wire) (long borrow : Wire) : Program :=
  (notRegister M).reverse ++ PortalUnitInverse.emit M C borrow ++ (notRegister M).reverse ++
    (copyRegister (some long) A M).reverse

theorem restore_undo (A M C : List Wire) (long borrow : Wire)
    (L : Companion.Geometry A M C long borrow)
    (proper : ProperProgram (copyRegister (some long) A M)) (flip : ProperProgram (notRegister M))
    (s : State) (m n : List Bool) (clean : ∀ q ∈ C, s.basis q = false) :
    run (restoreBack A M C long borrow) n (run (Companion.restore A M C long borrow) m s) = s := by
  let t := run (copyRegister (some long) A M) m s
  have copy := copyRegister_correct (some long) A M L.limbs L.copy
    (by intro c hc; obtain rfl := Option.mem_some_iff.mp hc; exact L.flag) s m
  have cm : ∀ q ∈ C, t.basis q=false := fun q h => (copy.2.1 q (L.scratch q h)).trans (clean q h)
  have nd := (List.nodup_append'.mp (List.nodup_cons.mp L.ripple).2).1
  have inv (x : List Bool) : ∀ q ∈ C, (run (notRegister M) x t).basis q = false := by
    intro q h
    rw [notRegister_correct _ nd]
    simpa only [if_neg (L.scratch q h)] using cm q h
  simp only [restoreBack, Companion.restore, HighBankUnit.sub, mappedSub, run_append, run_take]
  rw [run_reverse_proper _ flip]
  rw [show mappedAdd (HighBankUnit.zeros M.length) M C borrow=HighBankUnit.add M C borrow by rfl]
  rw [PortalUnitInverse.undo M C borrow L.carries L.ripple _ _ _ (inv _)]
  rw [run_reverse_proper _ flip, run_reverse_proper _ proper]

theorem mask_open (a b x t:Wire) (s:State) (m:List Bool) (nd:[a,b,x,t].Nodup)
    (hx:s.basis x=false) (ht:s.basis t=false) :
    run [.X x,.CX a x,.CCX b x t] m s =
      ⟨s.phase, writeBit (writeBit s.basis x (!s.basis a)) t (s.basis b && !s.basis a)⟩ := by
  obtain ⟨_,ax,_,bx,bt,xt⟩:a≠b ∧ a≠x ∧ a≠t ∧ b≠x ∧ b≠t ∧ x≠t := by simpa [and_assoc] using nd
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qt:q=t <;> by_cases qx:q=x <;> simp_all [writeBit,Function.update]

theorem mask_close (a b x t:Wire) (s:State) (m:List Bool) (nd:[a,b,x,t].Nodup)
    (hx:s.basis x=(!s.basis a)) (ht:s.basis t=(s.basis b && s.basis x)) :
    run [.measureX t [] [.CZ b x],.CX a x,.X x] m s =
      ⟨s.phase, writeBit (writeBit s.basis x false) t false⟩ := by
  obtain ⟨_,ax,at0,_,bt,xt⟩:a≠b ∧ a≠x ∧ a≠t ∧ b≠x ∧ b≠t ∧ x≠t := by simpa [and_assoc] using nd
  change run [.CX a x,.X x] (m.drop 1) (run [.measureX t [] [.CZ b x]] m s)=_
  rw [PortalAnd.measure_and _ _ _ _ _ bt xt ht]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qt:q=t <;> by_cases qx:q=x <;> simp_all [writeBit,Function.update]

theorem any_positive (qs : List Wire) (s : BasisState) :
    qs.any s = decide (0 < regValue qs s) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.any_cons, ih, regValue]
    cases h : s q <;> simp [h]

theorem high_three (a b : Wire) (qs : List (Wire × Wire)) (s : BasisState) :
    PortalAnd.high a b qs s = decide (3 ≤ regValue (a::b::qs.map Prod.fst) s) := by
  simp only [PortalAnd.high,any_positive,regValue]
  apply Bool.eq_iff_iff.mpr
  cases ha : s a <;> cases hb : s b <;> simp [ha,hb] <;> omega

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic MappedCompressed

structure Source (L:SkywalkIntegerLayout) (f:Wire→Wire) (k a b g:Nat) (pairs:List (Wire×Wire)) : Prop where
  left : (pairs.map Prod.fst).map f=L.a.drop k
  right : (pairs.map Prod.snd).map f=L.b.drop k
  aTop : f a=L.aSign
  bTop : f b=L.bSign
  previous : f g=L.previous
  aLength : k≤L.a.length
  bLength : k≤L.b.length

theorem scan_input (L:SkywalkIntegerLayout) (f:Wire→Wire) (k a b g n:Nat) (pairs:List (Wire×Wire))
    (src:Source L f k a b g pairs) (valid:RailPair.ScanGeometry a b g n pairs)
    (raw:State) (m:List Bool) (u v:Nat) (route sg:Bool)
    (input:SkywalkIntegerInput L (SkywalkRails.encode route sg u v).a (SkywalkRails.encode route sg u v).b route raw.basis)
    (clean:(pullState f raw).basis n=false) :
    let t:=run (RailPair.scan a b g n pairs) m (pullState f raw)
    let e:=negative sg u
    t.basis n=e ∧ t.basis g=route ∧ regValue (pairs.map Prod.fst) t.basis=(u+v)/2^k ∧
    regValue (pairs.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let st:=pullState f raw
  have math:=mathematical L route sg u v raw.basis input
  have gg:st.basis g=route:=(congrArg raw.basis src.previous).trans math.1
  have ss:(st.basis a ^^ st.basis b)=negative sg u:=by
    change (raw.basis (f a) ^^ raw.basis (f b))=_
    rw [src.aTop,src.bTop];exact math.2.1
  have out:=RailPair.scan_run _ _ _ _ _ valid st m clean
  have values:=scan_values _ _ _ _ _ valid st m clean
  have nv:=List.nodup_cons.mp valid.unique
  have outside:g∉RailPair.sites pairs:=(List.nodup_cons.mp nv.2).1
  have gn:g≠n:=fun eq=>nv.1 (List.mem_cons.mpr (Or.inl eq.symm))
  have lift (rs:List Wire) (b:BasisState):regValue rs (fun q=>b (f q))=regValue (rs.map f) b:=(unroute f rs b).symm
  have L0:regValue (pairs.map Prod.fst) st.basis=regValue L.a raw.basis/2^k:=by
    rw [show st.basis=fun q=>raw.basis (f q) by rfl,lift,src.left,shiftedValue _ _ src.aLength]
  have R0:regValue (pairs.map Prod.snd) st.basis=regValue L.b raw.basis/2^k:=by
    rw [show st.basis=fun q=>raw.basis (f q) by rfl,lift,src.right,shiftedValue _ _ src.bLength]
  let e:=negative sg u
  have L1:regValue (pairs.map Prod.fst) (fun q=>st.basis q ^^ e)=regValue L.a (fun q=>raw.basis q ^^ e)/2^k:=by
    rw [show (fun q=>st.basis q ^^ e)=(fun q=>(fun t=>raw.basis t ^^ e) (f q)) by rfl,lift (pairs.map Prod.fst) (fun t=>raw.basis t ^^ e),src.left,shiftedValue _ _ src.aLength]
  have R1:regValue (pairs.map Prod.snd) (fun q=>st.basis q ^^ e)=regValue L.b (fun q=>raw.basis q ^^ e)/2^k:=by
    rw [show (fun q=>st.basis q ^^ e)=(fun q=>(fun t=>raw.basis t ^^ e) (f q)) by rfl,lift (pairs.map Prod.snd) (fun t=>raw.basis t ^^ e),src.right,shiftedValue _ _ src.bLength]
  refine ⟨out.2.1.trans ss,(out.2.2.1 g gn outside).trans gg,?_⟩
  obtain ⟨pos,mag⟩:=math.2.2
  dsimp only at values
  rw [gg,ss] at values
  cases route <;> simp only [wordPos,wordSigned,ite_true,Bool.false_eq_true,ite_false] at pos mag values
  · exact ⟨values.1.trans (L0.trans (congrArg (· /2^k) pos)),values.2.trans (R1.trans (congrArg (· /2^k) mag))⟩
  · exact ⟨values.1.trans (R0.trans (congrArg (· /2^k) pos)),values.2.trans (L1.trans (congrArg (· /2^k) mag))⟩

theorem real_input (d:Bool) (x p i:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p) (hi:i<512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) :
    let z:=SkywalkNat.step^[i] (SkywalkNat.init x p)
    ∃ g sg:Bool, SkywalkIntegerInput (W.compactSkywalkTickLayout base i)
      (SkywalkRails.encode g sg z.u z.v).a (SkywalkRails.encode g sg z.u z.v).b g s.basis := by
  obtain ⟨g,sg,eq⟩:=SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  have source:=original_input d x p i hp0 hx0 hpo hp hq hx hc hi s stage
  change SkywalkIntegerInput _ (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).a
    (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).b
    (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).g _ at source
  change SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)=_ at eq
  rw [eq] at source
  refine ⟨g,sg,?_⟩
  cases g <;> exact source

#print axioms scan_input
#print axioms real_input
end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave225Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def ys : List Wire := [1718, 1719, 1720, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042]
def carries : List Wire := [1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693]

theorem emitted : ((leave225.drop 334).take 483) = adjust ys carries 1724 1597 := by rfl
theorem combined : ((leave225.drop 334).take 1744) =
    adjust ys carries 1724 1597 ++ ((leave225.drop 817).take 1261) := by rfl

theorem result (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (one : ∀ q ∈ Leave225Join.tags, s.basis q = decide (q = Leave225Join.tags.getD key 0)) :
    let x := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    Result wire 112 (x <<< key.val) s (run ((leave225.drop 334).take 1744) m s) := by
  let p := adjust ys carries 1724 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1724 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 97, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 112, 97 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^97 := regValue_lt ys t.basis
  have data : holds wire 112 x t := by
    intro i hi
    by_cases lo : i < 97
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 97 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave225Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave225Join.tags, t.basis q = decide (q = Leave225Join.tags.getD key 0) :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (one _ h)
  have action := value key x t (m.drop (measurementCount p)) small data cold keys
  have initial : x = adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨action.bits,action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 97 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave225High

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Word
open Partial Leave225Join Leave225Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev row (i : Fin 18) := columns[i.val]'(i.isLt)
def hot (key : Fin 16) (q : Wire) := decide (q = tags.getD key 0)

theorem combine (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis 1724).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614=false) :
    let out := run ((leave225.drop 2080).take 108) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref := hot key
  let u := run digitPass m s
  have sch : ∀ key : Fin 16, schedule (hot key) key false 0 columns = true := by decide +kernel
  have unique : ∀ i t : Fin 16, hot t (tags.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i<0+16) : s.basis (tags.getD i 0)=decide (i=key.val) := by
    have mem : tags.getD i 0 ∈ tags := by rw [List.getD_eq_getElem _ _ (show i<tags.length from hi)]; exact List.getElem_mem _
    exact (tagsOn _ mem).trans (unique ⟨i,hi⟩ key)
  have z := digits_remainder digitSites s m key.val (by omega) key.isLt sel X 18 (by decide)
    (fun i _ j _ eq => Nat.add_left_cancel eq) shadow digit
  have geom : ∀ i : Fin 18, (row i).shadow=401+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have hits : ∀ r ∈ columns, ∀ q ∈ r.hot, q∈tags := by decide +kernel
  have members : ∀ q ∈ tags, ∀ i : Fin 18, q≠401+i.val := by decide +kernel
  have tx : ∀ i j : Fin 18, wire i.val ≠ 401+j.val := by decide +kernel
  have cold : ∀ i : Fin 18, 1614 ≠ 401+i.val := by decide +kernel
  have ctrl : ∀ r∈columns, ∀ q∈r.hot, u.basis q=ref q := by
    intro r hr q hq
    have mem := hits r hr q hq
    exact (z.2.2 q (members q mem ⟨key.val,by omega⟩) (members q mem ⟨key.val+1,by omega⟩)).trans (tagsOn q mem)
  have inputs : columnsRead columns u.basis X H key.val 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change u.basis (row ix).shadow = _ ∧ u.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.zero_add]
    exact ⟨z.2.1 i hi,(z.2.2 _ (tx ix ⟨key.val,by omega⟩) (tx ix ⟨key.val+1,by omega⟩)).trans (tube i hi)⟩
  have rz : u.basis 1614=false :=
    (z.2.2 _ (cold ⟨key.val,by omega⟩) (cold ⟨key.val+1,by omega⟩)).trans scratch
  have word := reassemble 1614 columns ref u m X H key.val sites disjoint ctrl rz (sch key) inputs
  dsimp only
  rw [Leave225Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero]
  refine ⟨word.1.trans z.1,fun i => word.2.1 i.val i.isLt,?_⟩
  intro q away
  have safe (j : Fin 18) : q ≠ 401+j.val := by
    rw [← (geom j).1]
    exact (away _ (List.getElem_mem j.isLt)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe ⟨key.val,by omega⟩) (safe ⟨key.val+1,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave225Word

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave240Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def ys : List Wire := [1710, 1711, 1712, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042]
def carries : List Wire := [1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701]

theorem emitted : ((leave240.drop 334).take 523) = adjust ys carries 1716 1597 := by rfl
theorem combined : ((leave240.drop 334).take 1880) =
    adjust ys carries 1716 1597 ++ ((leave240.drop 857).take 1357) := by rfl

theorem result (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (one : ∀ q ∈ Leave240Join.tags, s.basis q = decide (q = Leave240Join.tags.getD key 0)) :
    let x := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    Result wire 120 (x <<< key.val) s (run ((leave240.drop 334).take 1880) m s) := by
  let p := adjust ys carries 1716 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1716 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 105, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 120, 105 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^105 := regValue_lt ys t.basis
  have data : holds wire 120 x t := by
    intro i hi
    by_cases lo : i < 105
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 105 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave240Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave240Join.tags, t.basis q = decide (q = Leave240Join.tags.getD key 0) :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (one _ h)
  have action := value key x t (m.drop (measurementCount p)) small data cold keys
  have initial : x = adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨action.bits,action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 105 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave240High

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Word
open Partial Leave240Join Leave240Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
abbrev row (i : Fin 18) := columns[i.val]'(i.isLt)
def hot (key : Fin 16) (q : Wire) := decide (q = tags.getD key 0)

theorem combine (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis 1716).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614=false) :
    let out := run ((leave240.drop 2216).take 107) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref := hot key
  let u := run digitPass m s
  have sch : ∀ key : Fin 16, schedule (hot key) key false 0 columns = true := by decide +kernel
  have unique : ∀ i t : Fin 16, hot t (tags.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i<0+16) : s.basis (tags.getD i 0)=decide (i=key.val) := by
    have mem : tags.getD i 0 ∈ tags := by rw [List.getD_eq_getElem _ _ (show i<tags.length from hi)]; exact List.getElem_mem _
    exact (tagsOn _ mem).trans (unique ⟨i,hi⟩ key)
  have z := digits_remainder digitSites s m key.val (by omega) key.isLt sel X 18 (by decide)
    (fun i _ j _ eq => Nat.add_left_cancel eq) shadow digit
  have geom : ∀ i : Fin 18, (row i).shadow=408+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have hits : ∀ r ∈ columns, ∀ q ∈ r.hot, q∈tags := by decide +kernel
  have members : ∀ q ∈ tags, ∀ i : Fin 18, q≠408+i.val := by decide +kernel
  have tx : ∀ i j : Fin 18, wire i.val ≠ 408+j.val := by decide +kernel
  have cold : ∀ i : Fin 18, 1614 ≠ 408+i.val := by decide +kernel
  have ctrl : ∀ r∈columns, ∀ q∈r.hot, u.basis q=ref q := by
    intro r hr q hq
    have mem := hits r hr q hq
    exact (z.2.2 q (members q mem ⟨key.val,by omega⟩) (members q mem ⟨key.val+1,by omega⟩)).trans (tagsOn q mem)
  have inputs : columnsRead columns u.basis X H key.val 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change u.basis (row ix).shadow = _ ∧ u.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.zero_add]
    exact ⟨z.2.1 i hi,(z.2.2 _ (tx ix ⟨key.val,by omega⟩) (tx ix ⟨key.val+1,by omega⟩)).trans (tube i hi)⟩
  have rz : u.basis 1614=false :=
    (z.2.2 _ (cold ⟨key.val,by omega⟩) (cold ⟨key.val+1,by omega⟩)).trans scratch
  have word := reassemble 1614 columns ref u m X H key.val sites disjoint ctrl rz (sch key) inputs
  dsimp only
  rw [Leave240Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero]
  refine ⟨word.1.trans z.1,fun i => word.2.1 i.val i.isLt,?_⟩
  intro q away
  have safe (j : Fin 18) : q ≠ 408+j.val := by
    rw [← (geom j).1]
    exact (away _ (List.getElem_mem j.isLt)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe ⟨key.val,by omega⟩) (safe ⟨key.val+1,by omega⟩))

end ECDSAAdd.Entrant.StairPacket.Leave240Word

end

section

open ECDSAAdd.Arithmetic
set_option maxRecDepth 32000
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
theorem erase_run (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (input:(regValue fullM s.basis+(s.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) s.basis (regValue fullA s.basis)) :
    (run erase m s).phase=s.phase ∧ (∀q,q∉fullM → (run erase m s).basis q=s.basis q) ∧ regValue fullM (run erase m s).basis=0 := by
  rw [erase_eq]
  exact Companion.clear fullA fullM fullC 1556 1558 full_geometry s m clean input
theorem erase_roundtrip (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (n:List Bool) : run eraseBack n (run erase m s)=s := by
  rw [eraseBack_eq,erase_eq]
  apply LeaveCompanion.erase_undo fullA fullM fullC 1556 1558 full_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem restore_run (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (input:regValue smallM s.basis=0) :
    (run restore m s).phase=s.phase ∧ (∀q,q∉smallM → (run restore m s).basis q=s.basis q) ∧ regValue smallM (run restore m s).basis=(copyValue (some 1556) s.basis (regValue smallA s.basis)+2^smallM.length-(s.basis 1558).toNat)%2^smallM.length := by
  rw [restore_eq]
  exact Companion.write smallA smallM smallC 1556 1558 small_geometry s m clean input
theorem restore_roundtrip (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (n:List Bool) : run restoreBack n (run restore m s)=s := by
  rw [restoreBack_eq,restore_eq]
  apply LeaveCompanion.restore_undo smallA smallM smallC 1556 1558 small_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem pending_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (408::409::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pending_run s m fresh clean, LeaveCompanion.high_three]
theorem pendingBack_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (408::409::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pendingBack_run s m fresh clean, LeaveCompanion.high_three]
theorem nextU_run (s:State) (m:List Bool) (fresh:s.basis 1558=false) :
    run nextU m s=⟨s.phase,writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  rw [nextU_eq]
  simp [run,fresh]
theorem nextUBack_run (s:State) (m:List Bool) (product:s.basis 1558=(s.basis 1556 && s.basis 1557)) :
    run nextUBack m s=⟨s.phase,writeBit s.basis 1558 false⟩ := by
  rw [nextUBack_eq]
  exact PortalAnd.measure_and _ _ _ _ _ (by decide) (by decide) product
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
theorem erase_run (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (input:(regValue fullM s.basis+(s.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) s.basis (regValue fullA s.basis)) :
    (run erase m s).phase=s.phase ∧ (∀q,q∉fullM → (run erase m s).basis q=s.basis q) ∧ regValue fullM (run erase m s).basis=0 := by
  rw [erase_eq]
  exact Companion.clear fullA fullM fullC 1556 1558 full_geometry s m clean input
theorem erase_roundtrip (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (n:List Bool) : run eraseBack n (run erase m s)=s := by
  rw [eraseBack_eq,erase_eq]
  apply LeaveCompanion.erase_undo fullA fullM fullC 1556 1558 full_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem restore_run (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (input:regValue smallM s.basis=0) :
    (run restore m s).phase=s.phase ∧ (∀q,q∉smallM → (run restore m s).basis q=s.basis q) ∧ regValue smallM (run restore m s).basis=(copyValue (some 1556) s.basis (regValue smallA s.basis)+2^smallM.length-(s.basis 1558).toNat)%2^smallM.length := by
  rw [restore_eq]
  exact Companion.write smallA smallM smallC 1556 1558 small_geometry s m clean input
theorem restore_roundtrip (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (n:List Bool) : run restoreBack n (run restore m s)=s := by
  rw [restoreBack_eq,restore_eq]
  apply LeaveCompanion.restore_undo smallA smallM smallC 1556 1558 small_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem pending_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (416::417::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pending_run s m fresh clean, LeaveCompanion.high_three]
theorem pendingBack_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (416::417::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pendingBack_run s m fresh clean, LeaveCompanion.high_three]
theorem nextU_run (s:State) (m:List Bool) (fresh:s.basis 1558=false) :
    run nextU m s=⟨s.phase,writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  rw [nextU_eq]
  simp [run,fresh]
theorem nextUBack_run (s:State) (m:List Bool) (product:s.basis 1558=(s.basis 1556 && s.basis 1557)) :
    run nextUBack m s=⟨s.phase,writeBit s.basis 1558 false⟩ := by
  rw [nextUBack_eq]
  exact PortalAnd.measure_and _ _ _ _ _ (by decide) (by decide) product
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
theorem erase_run (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (input:(regValue fullM s.basis+(s.basis 1558).toNat)%2^fullM.length=copyValue (some 1556) s.basis (regValue fullA s.basis)) :
    (run erase m s).phase=s.phase ∧ (∀q,q∉fullM → (run erase m s).basis q=s.basis q) ∧ regValue fullM (run erase m s).basis=0 := by
  rw [erase_eq]
  exact Companion.clear fullA fullM fullC 1556 1558 full_geometry s m clean input
theorem erase_roundtrip (s:State) (m:List Bool) (clean:∀q∈fullC,s.basis q=false) (n:List Bool) : run eraseBack n (run erase m s)=s := by
  rw [eraseBack_eq,erase_eq]
  apply LeaveCompanion.erase_undo fullA fullM fullC 1556 1558 full_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem restore_run (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (input:regValue smallM s.basis=0) :
    (run restore m s).phase=s.phase ∧ (∀q,q∉smallM → (run restore m s).basis q=s.basis q) ∧ regValue smallM (run restore m s).basis=(copyValue (some 1556) s.basis (regValue smallA s.basis)+2^smallM.length-(s.basis 1558).toNat)%2^smallM.length := by
  rw [restore_eq]
  exact Companion.write smallA smallM smallC 1556 1558 small_geometry s m clean input
theorem restore_roundtrip (s:State) (m:List Bool) (clean:∀q∈smallC,s.basis q=false) (n:List Bool) : run restoreBack n (run restore m s)=s := by
  rw [restoreBack_eq,restore_eq]
  apply LeaveCompanion.restore_undo smallA smallM smallC 1556 1558 small_geometry <;> first | exact clean | exact PortalStatic.proper _ (by decide +kernel)
theorem pending_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pending m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (423::424::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pending_run s m fresh clean, LeaveCompanion.high_three]
theorem pendingBack_three (s:State) (m:List Bool) (fresh:s.basis 1558=false) (clean:∀p∈pendingPairs,s.basis p.2=false) :
    run pendingBack m s=⟨s.phase,writeBit s.basis 1557 (s.basis 1557 ^^ decide (3≤regValue (423::424::pendingPairs.map Prod.fst) s.basis))⟩ := by
  rw [pendingBack_run s m fresh clean, LeaveCompanion.high_three]
theorem nextU_run (s:State) (m:List Bool) (fresh:s.basis 1558=false) :
    run nextU m s=⟨s.phase,writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  rw [nextU_eq]
  simp [run,fresh]
theorem nextUBack_run (s:State) (m:List Bool) (product:s.basis 1558=(s.basis 1556 && s.basis 1557)) :
    run nextUBack m s=⟨s.phase,writeBit s.basis 1558 false⟩ := by
  rw [nextUBack_eq]
  exact PortalAnd.measure_and _ _ _ _ _ (by decide) (by decide) product
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end



section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open LeaveSelector
def ports : Ports := ⟨271,416,1709,1710⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem controlCert : ∀k : Mode, reads ports (sim prepare (LeaveSelector.start ports false k))=controls ports k := by decide +kernel
theorem controlInvCert : ∀k : Mode, reads ports (sim prepareInv (LeaveSelector.start ports true k))=controls ports k := by decide +kernel
theorem cleanCert : ∀k : Mode, targetCert ports prepare retire false k=true := by decide +kernel
theorem cleanInvCert : ∀k : Mode, targetCert ports prepare retireInv true k=true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end


section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

/-- Compression keeps the top test of the unsigned magnitude unless the
    retained part wraps. That case is marked by the next far indicator. -/
theorem retain_flag (half bound mag : Nat) (far : Bool) (width : half ≤ bound)
    (near : far = false → mag < bound) :
    ((decide (half ≤ mag) && far) || decide (half ≤ mag % bound)) =
      decide (half ≤ mag) := by
  cases far with
  | false => simp [Nat.mod_eq_of_lt (near rfl)]
  | true =>
    by_cases h : half ≤ mag
    · simp [h]
    · have l : mag < bound := by omega
      simp [h,Nat.mod_eq_of_lt l]

/-- The observed unsigned endpoint may be `u-1` for a negative ordinate.
    At a far threshold, a one-bit sign offset cannot change its long-rail tag. -/
theorem far_orientation (half u v sign : Nat) (signBit : sign≤1) (small : min u v<half)
    (far : 2*half < u+v) : (half ≤ u-sign) ↔ (half ≤ u) := by omega

/-- Converting a post-merge magnitude to a physical lower limb and sign bit
    gives the exact threshold test even when the whole magnitude has wrapped. -/
theorem lower_nonzero (half limb mag : Nat) (hp : 0 < half)  :
    (decide (half ≤ mag % (2*half)) || decide (0 < (mag / (2*half)) % limb)) =
      decide (half ≤ mag % ((2*half)*limb)) := by
  let r := mag % ((2*half)*limb)
  have bottom : r % (2*half)=mag%(2*half) :=
    Nat.mod_mod_of_dvd mag (dvd_mul_right (2*half) limb)
  have top : r / (2*half)=(mag/(2*half))%limb := Nat.mod_mul_right_div_self _ _ _
  rw [←bottom,←top]
  change (_ || _) = decide (half ≤ r)
  by_cases h : r < 2*half
  · simp [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
  · have pos : 0 < r/(2*half) := Nat.div_pos (by omega) (by omega)
    simp [pos,show half ≤ r by omega]

def upperBorrow (half u v sign : Nat) : Nat :=
  if half ≤ (u-sign)%(2*half) ∧ (u+v)%(2*half)<half then 1 else 0

/-- Before the merge, adding the physical borrow to M cancels the
    enabled copy of A in the pre-merge register, modulo its actual width. -/
theorem upper_clear (half u v sign radix : Nat) (hp : 0<half)
    (se : sign≤1) (su : sign≤u) (small : min u v<half) :
    (((u-sign)/(2*half))%radix+upperBorrow half u v sign)%radix =
    (if half ≤ u-sign then ((u+v)/(2*half))%radix else 0) := by
  have hc := companion_upper half u v sign hp se su small
  dsimp only at hc
  by_cases h : half ≤ u-sign
  · simp only [if_pos h] at hc ⊢
    rw [hc, Nat.mod_add_mod]
    rfl
  · simp only [if_neg h] at hc ⊢
    have lt : u-sign<2*half := by omega
    simp [hc,upperBorrow,Nat.mod_eq_of_lt lt,h]

/-- After copying the corrected positive rail, subtraction of the same single
    borrow reconstructs precisely the retained magnitude, including wrap. -/
theorem upper_restore (half u v sign radix : Nat) (hp : 0<half)
    (se : sign≤1) (su : sign≤u) (small : min u v<half) (rp : 0<radix) :
    ((if half≤u-sign then ((u+v)/(2*half))%radix else 0)+radix-
        upperBorrow half u v sign)%radix = ((u-sign)/(2*half))%radix := by
  rw [←upper_clear half u v sign radix hp se su small]
  let y := ((u-sign)/(2*half))%radix
  let b := upperBorrow half u v sign
  have by1 : b≤1 := by dsimp [b,upperBorrow]; split <;> omega
  have yl : y<radix := Nat.mod_lt _ rp
  change ((y+b)%radix+radix-b)%radix=y
  rw [show (y+b)%radix+radix-b=(y+b)%radix+(radix-b) by omega,
    Nat.mod_add_mod,show y+b+(radix-b)=y+radix by omega,Nat.add_mod_right,
    Nat.mod_eq_of_lt yl]

theorem near_bound (u v sign divisor bound : Nat) (dp : 0<divisor) (wide : 3*divisor≤bound)
    (near : decide (3≤(u+v)/divisor)=false) : u-sign<bound := by
  have lo : (u+v)/divisor<3 := by simpa using near
  have lim := (Nat.div_lt_iff_lt_mul dp).mp lo
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private theorem select (i:Nat) (scratch:List Wire) (pool:∀q∈scratch,OB5.sig (i-1) q∈(W.compactSkywalkTickLayout base i).carry)
    (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (hi:i<512) (s:State)
    (h:Rolling1588.Integer.Stage base d x p i s.basis) : ∀q∈scratch,(pullState (OB5.sig (i-1)) s).basis q=false:=by
  have input:=original_input d x p i hp0 hx0 hpo hp hq hx hc hi s h
  exact fun q hq=>(regValue_zero _ _).mp input.2.2.2.2.2 _ (pool q hq)

theorem enter225_clean (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p) (s:State) (h:Rolling1588.Integer.Stage base d x p 225 s.basis) :
    ∀q∈Portal225Flag.activeScratch,(pullState (OB5.sig 224) s).basis q=false:=
  select 225 _ (by decide +kernel) d x p hp0 hx0 hpo hp hq hx hc (by decide) s h

theorem enter270_clean (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p) (s:State) (h:Rolling1588.Integer.Stage base d x p 270 s.basis) :
    ∀q∈Portal270Flag.activeScratch,(pullState (OB5.sig 269) s).basis q=false:=
  select 270 _ (by decide +kernel) d x p hp0 hx0 hpo hp hq hx hc (by decide) s h
#print axioms enter225_clean
#print axioms enter270_clean
end ECDSAAdd.Entrant.StairPacket

end


section

open ECDSAAdd.Arithmetic
set_option maxRecDepth 32000
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
theorem clearFlag_digits : PortalAnd.digits 1558 clearFlagPairs = 1558::930::smallM := by decide +kernel
theorem clearFlag_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 930=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlag m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlag_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 930=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_reconstruct (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=false)
    (orientation:s.basis 1558=(decide (half≤mag) && s.basis 1557))
    (bottom:s.basis 930=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 (decide (half≤mag))⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
theorem clearFlag_digits : PortalAnd.digits 1558 clearFlagPairs = 1558::922::smallM := by decide +kernel
theorem clearFlag_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 922=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlag m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlag_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 922=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_reconstruct (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=false)
    (orientation:s.basis 1558=(decide (half≤mag) && s.basis 1557))
    (bottom:s.basis 922=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 (decide (half≤mag))⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
theorem clearFlag_digits : PortalAnd.digits 1558 clearFlagPairs = 1558::915::smallM := by decide +kernel
theorem clearFlag_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 915=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlag m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlag_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_value (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=decide (half≤mag))
    (orientation:s.basis 1558=(s.basis 1556 && s.basis 1557))
    (bottom:s.basis 915=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 false⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
theorem clearFlagBack_reconstruct (s:State) (m:List Bool) (half mag:Nat) (hp:0<half)
    (clean:∀p∈clearFlagPairs,s.basis p.2=false)
    (near:s.basis 1557=false → mag<(2*half)*2^smallM.length)
    (longBit:s.basis 1556=false)
    (orientation:s.basis 1558=(decide (half≤mag) && s.basis 1557))
    (bottom:s.basis 915=decide (half≤mag%(2*half)))
    (upper:regValue smallM s.basis=(mag/(2*half))%2^smallM.length) :
    run clearFlagBack m s=⟨s.phase,writeBit s.basis 1556 (decide (half≤mag))⟩ := by
  have width : half≤(2*half)*2^smallM.length := by
    have pow : 1≤2^smallM.length := Nat.one_le_two_pow
    have prod := Nat.mul_le_mul_left (2*half) pow
    omega
  rw [clearFlagBack_run s m clean,clearFlag_digits]
  simp only [List.any_cons,LeaveCompanion.any_positive,upper,bottom,orientation,longBit]
  rw [LeaveCompanion.lower_nonzero half _ mag hp,LeaveCompanion.retain_flag half _ mag _ width near]
  simp
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 225) (OB5.sig 224) 160 497 1042 240 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 497 1042 240 1723 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 497 1042 240 1723 pairs := by decide +kernel
theorem scan_real (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (s:State) (m:List Bool) (h:Rolling1588.Integer.Stage base d x p 225 s.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init x p)
    let v:=run scan m (pullState (OB5.sig 224) s)
    ∃g sg:Bool,v.basis 1723=negative sg z.u ∧ v.basis 240=g ∧ regValue railA v.basis=(z.u+z.v)/2^160 ∧
      regValue railB v.basis=(z.u-(negative sg z.u).toNat)/2^160 := by
  obtain ⟨route,sg,inp⟩:=real_input d x p 225 hp0 hx0 hpo hp hq hx hc (by decide) s h
  have clean: (pullState (OB5.sig 224) s).basis 1723=false := by
    apply (regValue_zero _ _).mp inp.2.2.2.2.2 (OB5.sig 224 1723)
    decide +kernel
  have v:=scan_input _ _ _ _ _ _ _ _ source geom s m _ _ _ _ inp clean
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at v
  exact ⟨route,sg,v⟩
#print axioms scan_real
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 270) (OB5.sig 269) 137 528 1028 285 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 528 1028 285 1700 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 528 1028 285 1700 pairs := by decide +kernel
theorem scan_real (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (s:State) (m:List Bool) (h:Rolling1588.Integer.Stage base d x p 270 s.basis) :
    let z:=SkywalkNat.step^[270] (SkywalkNat.init x p)
    let v:=run scan m (pullState (OB5.sig 269) s)
    ∃g sg:Bool,v.basis 1700=negative sg z.u ∧ v.basis 285=g ∧ regValue railA v.basis=(z.u+z.v)/2^137 ∧
      regValue railB v.basis=(z.u-(negative sg z.u).toNat)/2^137 := by
  obtain ⟨route,sg,inp⟩:=real_input d x p 270 hp0 hx0 hpo hp hq hx hc (by decide) s h
  have clean: (pullState (OB5.sig 269) s).basis 1700=false := by
    apply (regValue_zero _ _).mp inp.2.2.2.2.2 (OB5.sig 269 1700)
    decide +kernel
  have v:=scan_input _ _ _ _ _ _ _ _ source geom s m _ _ _ _ inp clean
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at v
  exact ⟨route,sg,v⟩
#print axioms scan_real
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192
def input : Cols := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
def output : Cols := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x33333333cccccccc33333333cccccccc33333333cccccccc33333333cccccccc000000000000000000000000000000000000000000000000000000000000000033333333cccccccc33333333cccccccc33333333cccccccc33333333cccccccc0000000000000000000000000000000000000000000000000000000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000000000000000000000000000000000000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000000000000000000000000000000000000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0a5a5f0f0f0f00f0f5a5a0f0f0f0ff0f0a5a5f0f0f0f00f0f5a5a0f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f05a5af0f0f0f00f0fa5a50f0f0f0ff0f05a5af0f0f0f00f0fa5a50f0f0f0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff41be00ff00ff00ff05fa00ff11eeff00be41ff00ff00ff00fa05ff00ee11000000000000000000000000000000000000000000000000000000000000000000ff827d00ff00ff00ffa05f00ff8877ff007d82ff00ff00ff005fa0ff0077880000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0x33333333cccccccc33333333cccccccc33333333cccccccc33333333cccccccc000000000000000000000000000000000000000000000000000000000000000033333333cccccccc33333333cccccccc33333333cccccccc33333333ccccccccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0b4b4f0f0b4b40f0f4b4b0f0f4b4bf0f0b4b4f0f0b4b40f0f4b4b0f0f4b4bffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb4b4f0f0b4b4f0f04b4b0f0f4b4b0f0fb4b4f0f0b4b4f0f04b4b0f0f4b4b0f0fffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xff40bf00ff01fe00ff04fb00ff45baff00bf40ff00fe01ff00fb04ff00ba45000000000000000000000000000000000000000000000000000000000000000045ba00ff04fb00ff01fe00ff40bf00ffba45ff00fb04ff00fe01ff00bf40ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xff00be41ff00ff00ff00fa05ff00ee1100ff41be00ff00ff00ff05fa00ff11eeff00bf40ff00fe01ff00fb04ff00ba4500ff40bf00ff01fe00ff04fb00ff45ba00ff827d00ff00ff00ffa05f00ff8877ff007d82ff00ff00ff005fa0ff00778845ba00ff04fb00ff01fe00ff40bf00ffba45ff00fb04ff00fe01ff00bf40ff00ff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ffff00ff00ff00ff00ff00ff00ff00ff00, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
def mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def forward : Program := [.CX 0 4,
.CCX 8 4 0,
.CX 0 4,
.CX 1 5,
.CCX 8 5 1,
.CX 1 5,
.CX 2 6,
.CCX 8 6 2,
.CX 2 6,
.CX 3 7,
.CCX 8 7 3,
.CX 3 7,
.CX 9 4,
.CX 9 5,
.CX 9 6,
.CX 9 7,
.X 15,
.CX 0 15,
.CCX 4 15 16,
.CCX 16 11 17,
.CCX 5 17 18,
.CCX 6 18 19,
.CX 19 7,
.measureX 19 [] [.CZ 6 18],
.CX 18 6,
.measureX 18 [] [.CZ 5 17],
.CX 17 5,
.CCX 11 1 5,
.CCX 11 2 6,
.CCX 11 3 7,
.CX 1 18,
.CCX 10 18 1,
.CX 1 18,
.CX 2 19,
.CCX 10 19 2,
.CX 2 19,
.CX 3 20,
.CCX 10 20 3,
.CX 3 20,
.CX 10 2,
.CCX 11 1 5,
.CCX 11 2 6,
.CCX 11 3 7,
.X 5,
.X 6,
.X 7,
.CCX 5 17 21,
.CCX 6 21 22,
.CX 22 7,
.measureX 22 [] [.CZ 6 21],
.CX 21 6,
.measureX 21 [] [.CZ 5 17],
.CX 17 5,
.X 5,
.X 6,
.X 7,
.measureX 17 [] [.CZ 16 11],
.measureX 16 [] [.CZ 4 15],
.CX 0 15,
.X 15,
.CX 9 4,
.CX 9 5,
.CX 9 6,
.CX 9 7,
.CX 0 4,
.CCX 8 4 0,
.CX 0 4,
.CX 1 5,
.CCX 8 5 1,
.CX 1 5,
.CX 2 6,
.CCX 8 6 2,
.CX 2 6,
.CX 3 7,
.CCX 8 7 3,
.CX 3 7,
.CX 3 9,
.CX 7 9,
.CX 18 12,
.CX 12 18,
.CX 18 12,
.CX 19 13,
.CX 13 19,
.CX 19 13,
.CX 20 14,
.CX 14 20,
.CX 20 14]
theorem forward_checked : eval mask forward input=(true,output) := by decide +kernel
def backward : Program := [.CX 20 14,
.CX 14 20,
.CX 20 14,
.CX 19 13,
.CX 13 19,
.CX 19 13,
.CX 18 12,
.CX 12 18,
.CX 18 12,
.CX 7 9,
.CX 3 9,
.CX 3 7,
.CCX 8 7 3,
.CX 3 7,
.CX 2 6,
.CCX 8 6 2,
.CX 2 6,
.CX 1 5,
.CCX 8 5 1,
.CX 1 5,
.CX 0 4,
.CCX 8 4 0,
.CX 0 4,
.CX 9 7,
.CX 9 6,
.CX 9 5,
.CX 9 4,
.X 15,
.CX 0 15,
.CCX 4 15 16,
.CCX 16 11 17,
.X 7,
.X 6,
.X 5,
.CX 17 5,
.CCX 5 17 21,
.CX 21 6,
.CCX 6 21 22,
.CX 22 7,
.measureX 22 [] [.CZ 6 21],
.measureX 21 [] [.CZ 5 17],
.X 7,
.X 6,
.X 5,
.CCX 11 3 7,
.CCX 11 2 6,
.CCX 11 1 5,
.CX 10 2,
.CX 3 20,
.CCX 10 20 3,
.CX 3 20,
.CX 2 19,
.CCX 10 19 2,
.CX 2 19,
.CX 1 18,
.CCX 10 18 1,
.CX 1 18,
.CCX 11 3 7,
.CCX 11 2 6,
.CCX 11 1 5,
.CX 17 5,
.CCX 5 17 18,
.CX 18 6,
.CCX 6 18 19,
.CX 19 7,
.measureX 19 [] [.CZ 6 18],
.measureX 18 [] [.CZ 5 17],
.measureX 17 [] [.CZ 16 11],
.measureX 16 [] [.CZ 4 15],
.CX 0 15,
.X 15,
.CX 9 7,
.CX 9 6,
.CX 9 5,
.CX 9 4,
.CX 3 7,
.CCX 8 7 3,
.CX 3 7,
.CX 2 6,
.CCX 8 6 2,
.CX 2 6,
.CX 1 5,
.CCX 8 5 1,
.CX 1 5,
.CX 0 4,
.CCX 8 4 0,
.CX 0 4]
theorem backward_checked : eval mask backward output=(true,input) := by decide +kernel
def result (r : Nat) : Nat :=
  let ra:=r%16; let rb:=r/16%16; let g:=r.testBit 8; let neg:=r.testBit 9
  let f:=r.testBit 10; let u:=r.testBit 11
  let a:=if g then rb else ra; let m:=(if g then ra else rb) ^^^ (if neg then 15 else 0)
  let w:=if u && m.testBit 0 && !a.testBit 0 then 1 else 0
  let h:=a/2; let sh:=if f then 2 else h
  let sm:=((((m/2+w)%8) ^^^ (if u then h else 0) ^^^ (if u then sh else 0))+8-w)%8
  let x:=2*sh+a%2; let y:=(2*sm+m%2) ^^^ (if neg then 15 else 0)
  let l:=if g then y else x; let b:=if g then x else y
  l+16*b+256*g.toNat+512*(neg ^^ l.testBit 3 ^^ b.testBit 3).toNat+
    1024*f.toNat+2048*u.toNat+4096*f.toNat*h
def width : Nat := 23
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave255Hit Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

def program (inv : Bool) := if inv then leave255Inv else leave255
def initPC (inv : Bool) := if inv then 995 else 242
def retirePC (inv : Bool) := if inv then 3176 else 2445
def beforeWord (inv : Bool) := ((program inv).drop (initPC inv+33)).take (if inv then 37 else 59)
def afterWord (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 59 else 37)

theorem flags (inv : Bool) : ((program inv).drop (initPC inv)).take 3 =
    (flagOps 1706 1707 inv).map Op.enter := by cases inv <;> rfl


theorem firstHit (inv : Bool) : ((program inv).drop (initPC inv+3)).take 30 =
    putAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact written
  · exact hitsInv

theorem lastHit (inv : Bool) : ((program inv).drop (retirePC inv+(if inv then 59 else 37))).take 30 =
    dropAll 1560 swaps LeaveSelector.tags 0 15  := by
  cases inv
  · exact retireHits
  · exact Leave255Hit.retired

theorem separate (i : Nat) (hi:i<15) (j : Nat) (hj:j<15) : swaps i≠LeaveSelector.tags j := by
  have cert : ∀i j : Fin 15, swaps i≠LeaveSelector.tags j := by decide +kernel
  exact cert ⟨i,hi⟩ ⟨j,hj⟩

theorem execute (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(LeaveSelector.start ports inv k q).read v) :
    let out := run (beforeWord inv) m s
    out.phase=s.phase ∧ out.basis 1710=nearby k ∧
    out.basis 1709=(crossing ports k).read v ∧ out.basis 1596=(signExpr ports k).read v ∧
    out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  cases inv
  · exact physical ports prepare false k s m v input (controlCert k)
  · exact physical ports prepareInv true k s m v input (controlInvCert k)

theorem clear (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v) :
    run (afterWord inv) m s=⟨s.phase,fun q => (restored ports inv k q).read v⟩ := by
  cases inv
  · apply cleanup ports prepare retire false k s m v input (cleanCert k)
    have good : (prepare++retire).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)
  · apply cleanup ports prepare retireInv true k s m v input (cleanInvCert k)
    have good : (prepare++retireInv).all (fun o=>decide (o.dst∈affected ports))=true := by decide +kernel
    exact fun o h=>of_decide_eq_true (List.all_eq_true.mp good o h)


end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small:min u v<2^144) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^160) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^160) :
    let far:=decide (3*2^160≤u+v)
    let long:=decide (3*2^160≤u+v ∧ 2^144≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1721 far) 1722 long⟩ := by
  have act:=PortalValues.actual_flags 401 402 thresholdPairs orientationPairs 946 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^160) (2^144) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small:min u v<2^144) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^160) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^160)
    (mode:q.basis 1722=decide (3*2^160≤u+v ∧ 2^144≤u)) :
    let r:=run erase m q
    r.phase=q.phase ∧ (∀w,w∉bulkB → r.basis w=q.basis w) ∧ regValue bulkB r.basis=0 := by
  rw [erase_spec]
  apply PortalBorrow.erase_run
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fresh.1
  · exact fresh.2
  · apply PortalValues.input_eq 401 402 403 946 947 948 1722 bulkA bulkB q.basis (2^160) (2^144) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel
#print axioms flags_values
#print axioms erase_values
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small:min u v<2^121) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^137) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^137) :
    let far:=decide (3*2^137≤u+v)
    let long:=decide (3*2^137≤u+v ∧ 2^121≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1698 far) 1699 long⟩ := by
  have act:=PortalValues.actual_flags 423 424 thresholdPairs orientationPairs 923 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^137) (2^121) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small:min u v<2^121) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^137) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^137)
    (mode:q.basis 1699=decide (3*2^137≤u+v ∧ 2^121≤u)) :
    let r:=run erase m q
    r.phase=q.phase ∧ (∀w,w∉bulkB → r.basis w=q.basis w) ∧ regValue bulkB r.basis=0 := by
  rw [erase_spec]
  apply PortalBorrow.erase_run
  · exact copy_good
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact fresh.1
  · exact fresh.2
  · apply PortalValues.input_eq 423 424 425 923 924 925 1699 bulkA bulkB q.basis (2^137) (2^121) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel
#print axioms flags_values
#print axioms erase_values
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192
def ports225 : List Wire := [400, 401, 402, 403, 945, 946, 947, 948, 240, 1723, 1721, 1722, 1718, 1719, 1720, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
def map225 (q:Wire) := ports225.getD q 0
theorem inc225 : ∀ a b : Fin width, map225 a=map225 b → a=b := by decide +kernel
theorem emitted225 : Partial.enter225=renameProgram map225 forward := by decide +kernel
theorem emitted225Inv : Partial.enter225Inv=renameProgram map225 backward := by decide +kernel
def ports240 : List Wire := [407, 408, 409, 410, 937, 938, 939, 940, 255, 1715, 1713, 1714, 1710, 1711, 1712, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
def map240 (q:Wire) := ports240.getD q 0
theorem inc240 : ∀ a b : Fin width, map240 a=map240 b → a=b := by decide +kernel
theorem emitted240 : Partial.enter240=renameProgram map240 forward := by decide +kernel
theorem emitted240Inv : Partial.enter240Inv=renameProgram map240 backward := by decide +kernel
def ports255 : List Wire := [415, 416, 417, 418, 930, 931, 932, 933, 270, 1708, 1706, 1707, 1703, 1704, 1705, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563]
def map255 (q:Wire) := ports255.getD q 0
theorem inc255 : ∀ a b : Fin width, map255 a=map255 b → a=b := by decide +kernel
theorem emitted255 : Partial.enter255=renameProgram map255 forward := by decide +kernel
theorem emitted255Inv : Partial.enter255Inv=renameProgram map255 backward := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify

def Formula (r : Nat) : Prop :=
  ∀ q:Fin width,(get input q).testBit r=r.testBit q ∧ (get output q).testBit r=(result r).testBit q
instance (r:Nat) : Decidable (Formula r) := inferInstanceAs (Decidable (∀_:Fin width,_))

def Interval (lo n : Nat) : Prop := ∀ j : Fin n, Formula (lo+j)
instance (lo n:Nat) : Decidable (Interval lo n) := inferInstanceAs (Decidable (∀_:Fin n,_))

theorem combine (lo n : Nat) (a:Interval lo n) (b:Interval (lo+n) n) : Interval lo (n+n) := by
  intro j
  by_cases h:j.val<n
  · exact a ⟨j,h⟩
  · have hj:=j.isLt
    have rhs:=b ⟨j.val-n,by omega⟩
    change Formula (lo+n+(j.val-n)) at rhs
    change Formula (lo+j.val)
    rwa [show lo+n+(j.val-n)=lo+j.val by omega] at rhs
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
def rawPrefix (inv : Bool) := (program inv).take (initPC inv)
theorem historyShape : ∀ inv : Bool, ∀i : Fin 15,
    LeaveSelector.parityAt (ports.g+i) (rawPrefix inv)=some true ∧
    LeaveSelector.parityAt (swaps i) (rawPrefix inv)=some false := by decide +kernel

theorem history (inv : Bool) (i : Fin 15) (s : State) (m : List Bool) :
    let out:=run (rawPrefix inv) m s
    out.basis (ports.g+i)= !s.basis (ports.g+i) ∧ out.basis (swaps i)=s.basis (swaps i) := by
  obtain ⟨g,sw⟩:=historyShape inv i
  exact ⟨by simpa using polarity _ _ _ g s m,by simpa using polarity _ _ _ sw s m⟩
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 240 1723 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 240 1723 1721 1722 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1721 ∧ w≠1722 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1721 ∧ w≠1722 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 3).zip (railB.take 3)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 285 1700 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 285 1700 1698 1699 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1698 ∧ w≠1699 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1698 ∧ w≠1699 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part0_16 : Interval 0 16 := by decide +kernel
private theorem part16_16 : Interval 16 16 := by decide +kernel
private theorem part32_16 : Interval 32 16 := by decide +kernel
private theorem part48_16 : Interval 48 16 := by decide +kernel
private theorem part64_16 : Interval 64 16 := by decide +kernel
private theorem part80_16 : Interval 80 16 := by decide +kernel
private theorem part96_16 : Interval 96 16 := by decide +kernel
private theorem part112_16 : Interval 112 16 := by decide +kernel
private theorem part128_16 : Interval 128 16 := by decide +kernel
private theorem part144_16 : Interval 144 16 := by decide +kernel
private theorem part160_16 : Interval 160 16 := by decide +kernel
private theorem part176_16 : Interval 176 16 := by decide +kernel
private theorem part192_16 : Interval 192 16 := by decide +kernel
private theorem part208_16 : Interval 208 16 := by decide +kernel
private theorem part224_16 : Interval 224 16 := by decide +kernel
private theorem part240_16 : Interval 240 16 := by decide +kernel
theorem part0_256 : Interval 0 256 := (combine 0 128 (combine 0 64 (combine 0 32 (combine 0 16 part0_16 part16_16) (combine 32 16 part32_16 part48_16)) (combine 64 32 (combine 64 16 part64_16 part80_16) (combine 96 16 part96_16 part112_16))) (combine 128 64 (combine 128 32 (combine 128 16 part128_16 part144_16) (combine 160 16 part160_16 part176_16)) (combine 192 32 (combine 192 16 part192_16 part208_16) (combine 224 16 part224_16 part240_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part256_16 : Interval 256 16 := by decide +kernel
private theorem part272_16 : Interval 272 16 := by decide +kernel
private theorem part288_16 : Interval 288 16 := by decide +kernel
private theorem part304_16 : Interval 304 16 := by decide +kernel
private theorem part320_16 : Interval 320 16 := by decide +kernel
private theorem part336_16 : Interval 336 16 := by decide +kernel
private theorem part352_16 : Interval 352 16 := by decide +kernel
private theorem part368_16 : Interval 368 16 := by decide +kernel
private theorem part384_16 : Interval 384 16 := by decide +kernel
private theorem part400_16 : Interval 400 16 := by decide +kernel
private theorem part416_16 : Interval 416 16 := by decide +kernel
private theorem part432_16 : Interval 432 16 := by decide +kernel
private theorem part448_16 : Interval 448 16 := by decide +kernel
private theorem part464_16 : Interval 464 16 := by decide +kernel
private theorem part480_16 : Interval 480 16 := by decide +kernel
private theorem part496_16 : Interval 496 16 := by decide +kernel
theorem part256_256 : Interval 256 256 := (combine 256 128 (combine 256 64 (combine 256 32 (combine 256 16 part256_16 part272_16) (combine 288 16 part288_16 part304_16)) (combine 320 32 (combine 320 16 part320_16 part336_16) (combine 352 16 part352_16 part368_16))) (combine 384 64 (combine 384 32 (combine 384 16 part384_16 part400_16) (combine 416 16 part416_16 part432_16)) (combine 448 32 (combine 448 16 part448_16 part464_16) (combine 480 16 part480_16 part496_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part2560_16 : Interval 2560 16 := by decide +kernel
private theorem part2576_16 : Interval 2576 16 := by decide +kernel
private theorem part2592_16 : Interval 2592 16 := by decide +kernel
private theorem part2608_16 : Interval 2608 16 := by decide +kernel
private theorem part2624_16 : Interval 2624 16 := by decide +kernel
private theorem part2640_16 : Interval 2640 16 := by decide +kernel
private theorem part2656_16 : Interval 2656 16 := by decide +kernel
private theorem part2672_16 : Interval 2672 16 := by decide +kernel
private theorem part2688_16 : Interval 2688 16 := by decide +kernel
private theorem part2704_16 : Interval 2704 16 := by decide +kernel
private theorem part2720_16 : Interval 2720 16 := by decide +kernel
private theorem part2736_16 : Interval 2736 16 := by decide +kernel
private theorem part2752_16 : Interval 2752 16 := by decide +kernel
private theorem part2768_16 : Interval 2768 16 := by decide +kernel
private theorem part2784_16 : Interval 2784 16 := by decide +kernel
private theorem part2800_16 : Interval 2800 16 := by decide +kernel
theorem part2560_256 : Interval 2560 256 := (combine 2560 128 (combine 2560 64 (combine 2560 32 (combine 2560 16 part2560_16 part2576_16) (combine 2592 16 part2592_16 part2608_16)) (combine 2624 32 (combine 2624 16 part2624_16 part2640_16) (combine 2656 16 part2656_16 part2672_16))) (combine 2688 64 (combine 2688 32 (combine 2688 16 part2688_16 part2704_16) (combine 2720 16 part2720_16 part2736_16)) (combine 2752 32 (combine 2752 16 part2752_16 part2768_16) (combine 2784 16 part2784_16 part2800_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part2816_16 : Interval 2816 16 := by decide +kernel
private theorem part2832_16 : Interval 2832 16 := by decide +kernel
private theorem part2848_16 : Interval 2848 16 := by decide +kernel
private theorem part2864_16 : Interval 2864 16 := by decide +kernel
private theorem part2880_16 : Interval 2880 16 := by decide +kernel
private theorem part2896_16 : Interval 2896 16 := by decide +kernel
private theorem part2912_16 : Interval 2912 16 := by decide +kernel
private theorem part2928_16 : Interval 2928 16 := by decide +kernel
private theorem part2944_16 : Interval 2944 16 := by decide +kernel
private theorem part2960_16 : Interval 2960 16 := by decide +kernel
private theorem part2976_16 : Interval 2976 16 := by decide +kernel
private theorem part2992_16 : Interval 2992 16 := by decide +kernel
private theorem part3008_16 : Interval 3008 16 := by decide +kernel
private theorem part3024_16 : Interval 3024 16 := by decide +kernel
private theorem part3040_16 : Interval 3040 16 := by decide +kernel
private theorem part3056_16 : Interval 3056 16 := by decide +kernel
theorem part2816_256 : Interval 2816 256 := (combine 2816 128 (combine 2816 64 (combine 2816 32 (combine 2816 16 part2816_16 part2832_16) (combine 2848 16 part2848_16 part2864_16)) (combine 2880 32 (combine 2880 16 part2880_16 part2896_16) (combine 2912 16 part2912_16 part2928_16))) (combine 2944 64 (combine 2944 32 (combine 2944 16 part2944_16 part2960_16) (combine 2976 16 part2976_16 part2992_16)) (combine 3008 32 (combine 3008 16 part3008_16 part3024_16) (combine 3040 16 part3040_16 part3056_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part3072_16 : Interval 3072 16 := by decide +kernel
private theorem part3088_16 : Interval 3088 16 := by decide +kernel
private theorem part3104_16 : Interval 3104 16 := by decide +kernel
private theorem part3120_16 : Interval 3120 16 := by decide +kernel
private theorem part3136_16 : Interval 3136 16 := by decide +kernel
private theorem part3152_16 : Interval 3152 16 := by decide +kernel
private theorem part3168_16 : Interval 3168 16 := by decide +kernel
private theorem part3184_16 : Interval 3184 16 := by decide +kernel
private theorem part3200_16 : Interval 3200 16 := by decide +kernel
private theorem part3216_16 : Interval 3216 16 := by decide +kernel
private theorem part3232_16 : Interval 3232 16 := by decide +kernel
private theorem part3248_16 : Interval 3248 16 := by decide +kernel
private theorem part3264_16 : Interval 3264 16 := by decide +kernel
private theorem part3280_16 : Interval 3280 16 := by decide +kernel
private theorem part3296_16 : Interval 3296 16 := by decide +kernel
private theorem part3312_16 : Interval 3312 16 := by decide +kernel
theorem part3072_256 : Interval 3072 256 := (combine 3072 128 (combine 3072 64 (combine 3072 32 (combine 3072 16 part3072_16 part3088_16) (combine 3104 16 part3104_16 part3120_16)) (combine 3136 32 (combine 3136 16 part3136_16 part3152_16) (combine 3168 16 part3168_16 part3184_16))) (combine 3200 64 (combine 3200 32 (combine 3200 16 part3200_16 part3216_16) (combine 3232 16 part3232_16 part3248_16)) (combine 3264 32 (combine 3264 16 part3264_16 part3280_16) (combine 3296 16 part3296_16 part3312_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part3328_16 : Interval 3328 16 := by decide +kernel
private theorem part3344_16 : Interval 3344 16 := by decide +kernel
private theorem part3360_16 : Interval 3360 16 := by decide +kernel
private theorem part3376_16 : Interval 3376 16 := by decide +kernel
private theorem part3392_16 : Interval 3392 16 := by decide +kernel
private theorem part3408_16 : Interval 3408 16 := by decide +kernel
private theorem part3424_16 : Interval 3424 16 := by decide +kernel
private theorem part3440_16 : Interval 3440 16 := by decide +kernel
private theorem part3456_16 : Interval 3456 16 := by decide +kernel
private theorem part3472_16 : Interval 3472 16 := by decide +kernel
private theorem part3488_16 : Interval 3488 16 := by decide +kernel
private theorem part3504_16 : Interval 3504 16 := by decide +kernel
private theorem part3520_16 : Interval 3520 16 := by decide +kernel
private theorem part3536_16 : Interval 3536 16 := by decide +kernel
private theorem part3552_16 : Interval 3552 16 := by decide +kernel
private theorem part3568_16 : Interval 3568 16 := by decide +kernel
theorem part3328_256 : Interval 3328 256 := (combine 3328 128 (combine 3328 64 (combine 3328 32 (combine 3328 16 part3328_16 part3344_16) (combine 3360 16 part3360_16 part3376_16)) (combine 3392 32 (combine 3392 16 part3392_16 part3408_16) (combine 3424 16 part3424_16 part3440_16))) (combine 3456 64 (combine 3456 32 (combine 3456 16 part3456_16 part3472_16) (combine 3488 16 part3488_16 part3504_16)) (combine 3520 32 (combine 3520 16 part3520_16 part3536_16) (combine 3552 16 part3552_16 part3568_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part3584_16 : Interval 3584 16 := by decide +kernel
private theorem part3600_16 : Interval 3600 16 := by decide +kernel
private theorem part3616_16 : Interval 3616 16 := by decide +kernel
private theorem part3632_16 : Interval 3632 16 := by decide +kernel
private theorem part3648_16 : Interval 3648 16 := by decide +kernel
private theorem part3664_16 : Interval 3664 16 := by decide +kernel
private theorem part3680_16 : Interval 3680 16 := by decide +kernel
private theorem part3696_16 : Interval 3696 16 := by decide +kernel
private theorem part3712_16 : Interval 3712 16 := by decide +kernel
private theorem part3728_16 : Interval 3728 16 := by decide +kernel
private theorem part3744_16 : Interval 3744 16 := by decide +kernel
private theorem part3760_16 : Interval 3760 16 := by decide +kernel
private theorem part3776_16 : Interval 3776 16 := by decide +kernel
private theorem part3792_16 : Interval 3792 16 := by decide +kernel
private theorem part3808_16 : Interval 3808 16 := by decide +kernel
private theorem part3824_16 : Interval 3824 16 := by decide +kernel
theorem part3584_256 : Interval 3584 256 := (combine 3584 128 (combine 3584 64 (combine 3584 32 (combine 3584 16 part3584_16 part3600_16) (combine 3616 16 part3616_16 part3632_16)) (combine 3648 32 (combine 3648 16 part3648_16 part3664_16) (combine 3680 16 part3680_16 part3696_16))) (combine 3712 64 (combine 3712 32 (combine 3712 16 part3712_16 part3728_16) (combine 3744 16 part3744_16 part3760_16)) (combine 3776 32 (combine 3776 16 part3776_16 part3792_16) (combine 3808 16 part3808_16 part3824_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part3840_16 : Interval 3840 16 := by decide +kernel
private theorem part3856_16 : Interval 3856 16 := by decide +kernel
private theorem part3872_16 : Interval 3872 16 := by decide +kernel
private theorem part3888_16 : Interval 3888 16 := by decide +kernel
private theorem part3904_16 : Interval 3904 16 := by decide +kernel
private theorem part3920_16 : Interval 3920 16 := by decide +kernel
private theorem part3936_16 : Interval 3936 16 := by decide +kernel
private theorem part3952_16 : Interval 3952 16 := by decide +kernel
private theorem part3968_16 : Interval 3968 16 := by decide +kernel
private theorem part3984_16 : Interval 3984 16 := by decide +kernel
private theorem part4000_16 : Interval 4000 16 := by decide +kernel
private theorem part4016_16 : Interval 4016 16 := by decide +kernel
private theorem part4032_16 : Interval 4032 16 := by decide +kernel
private theorem part4048_16 : Interval 4048 16 := by decide +kernel
private theorem part4064_16 : Interval 4064 16 := by decide +kernel
private theorem part4080_16 : Interval 4080 16 := by decide +kernel
theorem part3840_256 : Interval 3840 256 := (combine 3840 128 (combine 3840 64 (combine 3840 32 (combine 3840 16 part3840_16 part3856_16) (combine 3872 16 part3872_16 part3888_16)) (combine 3904 32 (combine 3904 16 part3904_16 part3920_16) (combine 3936 16 part3936_16 part3952_16))) (combine 3968 64 (combine 3968 32 (combine 3968 16 part3968_16 part3984_16) (combine 4000 16 part4000_16 part4016_16)) (combine 4032 32 (combine 4032 16 part4032_16 part4048_16) (combine 4064 16 part4064_16 part4080_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part512_16 : Interval 512 16 := by decide +kernel
private theorem part528_16 : Interval 528 16 := by decide +kernel
private theorem part544_16 : Interval 544 16 := by decide +kernel
private theorem part560_16 : Interval 560 16 := by decide +kernel
private theorem part576_16 : Interval 576 16 := by decide +kernel
private theorem part592_16 : Interval 592 16 := by decide +kernel
private theorem part608_16 : Interval 608 16 := by decide +kernel
private theorem part624_16 : Interval 624 16 := by decide +kernel
private theorem part640_16 : Interval 640 16 := by decide +kernel
private theorem part656_16 : Interval 656 16 := by decide +kernel
private theorem part672_16 : Interval 672 16 := by decide +kernel
private theorem part688_16 : Interval 688 16 := by decide +kernel
private theorem part704_16 : Interval 704 16 := by decide +kernel
private theorem part720_16 : Interval 720 16 := by decide +kernel
private theorem part736_16 : Interval 736 16 := by decide +kernel
private theorem part752_16 : Interval 752 16 := by decide +kernel
theorem part512_256 : Interval 512 256 := (combine 512 128 (combine 512 64 (combine 512 32 (combine 512 16 part512_16 part528_16) (combine 544 16 part544_16 part560_16)) (combine 576 32 (combine 576 16 part576_16 part592_16) (combine 608 16 part608_16 part624_16))) (combine 640 64 (combine 640 32 (combine 640 16 part640_16 part656_16) (combine 672 16 part672_16 part688_16)) (combine 704 32 (combine 704 16 part704_16 part720_16) (combine 736 16 part736_16 part752_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part768_16 : Interval 768 16 := by decide +kernel
private theorem part784_16 : Interval 784 16 := by decide +kernel
private theorem part800_16 : Interval 800 16 := by decide +kernel
private theorem part816_16 : Interval 816 16 := by decide +kernel
private theorem part832_16 : Interval 832 16 := by decide +kernel
private theorem part848_16 : Interval 848 16 := by decide +kernel
private theorem part864_16 : Interval 864 16 := by decide +kernel
private theorem part880_16 : Interval 880 16 := by decide +kernel
private theorem part896_16 : Interval 896 16 := by decide +kernel
private theorem part912_16 : Interval 912 16 := by decide +kernel
private theorem part928_16 : Interval 928 16 := by decide +kernel
private theorem part944_16 : Interval 944 16 := by decide +kernel
private theorem part960_16 : Interval 960 16 := by decide +kernel
private theorem part976_16 : Interval 976 16 := by decide +kernel
private theorem part992_16 : Interval 992 16 := by decide +kernel
private theorem part1008_16 : Interval 1008 16 := by decide +kernel
theorem part768_256 : Interval 768 256 := (combine 768 128 (combine 768 64 (combine 768 32 (combine 768 16 part768_16 part784_16) (combine 800 16 part800_16 part816_16)) (combine 832 32 (combine 832 16 part832_16 part848_16) (combine 864 16 part864_16 part880_16))) (combine 896 64 (combine 896 32 (combine 896 16 part896_16 part912_16) (combine 928 16 part928_16 part944_16)) (combine 960 32 (combine 960 16 part960_16 part976_16) (combine 992 16 part992_16 part1008_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part1024_16 : Interval 1024 16 := by decide +kernel
private theorem part1040_16 : Interval 1040 16 := by decide +kernel
private theorem part1056_16 : Interval 1056 16 := by decide +kernel
private theorem part1072_16 : Interval 1072 16 := by decide +kernel
private theorem part1088_16 : Interval 1088 16 := by decide +kernel
private theorem part1104_16 : Interval 1104 16 := by decide +kernel
private theorem part1120_16 : Interval 1120 16 := by decide +kernel
private theorem part1136_16 : Interval 1136 16 := by decide +kernel
private theorem part1152_16 : Interval 1152 16 := by decide +kernel
private theorem part1168_16 : Interval 1168 16 := by decide +kernel
private theorem part1184_16 : Interval 1184 16 := by decide +kernel
private theorem part1200_16 : Interval 1200 16 := by decide +kernel
private theorem part1216_16 : Interval 1216 16 := by decide +kernel
private theorem part1232_16 : Interval 1232 16 := by decide +kernel
private theorem part1248_16 : Interval 1248 16 := by decide +kernel
private theorem part1264_16 : Interval 1264 16 := by decide +kernel
theorem part1024_256 : Interval 1024 256 := (combine 1024 128 (combine 1024 64 (combine 1024 32 (combine 1024 16 part1024_16 part1040_16) (combine 1056 16 part1056_16 part1072_16)) (combine 1088 32 (combine 1088 16 part1088_16 part1104_16) (combine 1120 16 part1120_16 part1136_16))) (combine 1152 64 (combine 1152 32 (combine 1152 16 part1152_16 part1168_16) (combine 1184 16 part1184_16 part1200_16)) (combine 1216 32 (combine 1216 16 part1216_16 part1232_16) (combine 1248 16 part1248_16 part1264_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part1280_16 : Interval 1280 16 := by decide +kernel
private theorem part1296_16 : Interval 1296 16 := by decide +kernel
private theorem part1312_16 : Interval 1312 16 := by decide +kernel
private theorem part1328_16 : Interval 1328 16 := by decide +kernel
private theorem part1344_16 : Interval 1344 16 := by decide +kernel
private theorem part1360_16 : Interval 1360 16 := by decide +kernel
private theorem part1376_16 : Interval 1376 16 := by decide +kernel
private theorem part1392_16 : Interval 1392 16 := by decide +kernel
private theorem part1408_16 : Interval 1408 16 := by decide +kernel
private theorem part1424_16 : Interval 1424 16 := by decide +kernel
private theorem part1440_16 : Interval 1440 16 := by decide +kernel
private theorem part1456_16 : Interval 1456 16 := by decide +kernel
private theorem part1472_16 : Interval 1472 16 := by decide +kernel
private theorem part1488_16 : Interval 1488 16 := by decide +kernel
private theorem part1504_16 : Interval 1504 16 := by decide +kernel
private theorem part1520_16 : Interval 1520 16 := by decide +kernel
theorem part1280_256 : Interval 1280 256 := (combine 1280 128 (combine 1280 64 (combine 1280 32 (combine 1280 16 part1280_16 part1296_16) (combine 1312 16 part1312_16 part1328_16)) (combine 1344 32 (combine 1344 16 part1344_16 part1360_16) (combine 1376 16 part1376_16 part1392_16))) (combine 1408 64 (combine 1408 32 (combine 1408 16 part1408_16 part1424_16) (combine 1440 16 part1440_16 part1456_16)) (combine 1472 32 (combine 1472 16 part1472_16 part1488_16) (combine 1504 16 part1504_16 part1520_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part1536_16 : Interval 1536 16 := by decide +kernel
private theorem part1552_16 : Interval 1552 16 := by decide +kernel
private theorem part1568_16 : Interval 1568 16 := by decide +kernel
private theorem part1584_16 : Interval 1584 16 := by decide +kernel
private theorem part1600_16 : Interval 1600 16 := by decide +kernel
private theorem part1616_16 : Interval 1616 16 := by decide +kernel
private theorem part1632_16 : Interval 1632 16 := by decide +kernel
private theorem part1648_16 : Interval 1648 16 := by decide +kernel
private theorem part1664_16 : Interval 1664 16 := by decide +kernel
private theorem part1680_16 : Interval 1680 16 := by decide +kernel
private theorem part1696_16 : Interval 1696 16 := by decide +kernel
private theorem part1712_16 : Interval 1712 16 := by decide +kernel
private theorem part1728_16 : Interval 1728 16 := by decide +kernel
private theorem part1744_16 : Interval 1744 16 := by decide +kernel
private theorem part1760_16 : Interval 1760 16 := by decide +kernel
private theorem part1776_16 : Interval 1776 16 := by decide +kernel
theorem part1536_256 : Interval 1536 256 := (combine 1536 128 (combine 1536 64 (combine 1536 32 (combine 1536 16 part1536_16 part1552_16) (combine 1568 16 part1568_16 part1584_16)) (combine 1600 32 (combine 1600 16 part1600_16 part1616_16) (combine 1632 16 part1632_16 part1648_16))) (combine 1664 64 (combine 1664 32 (combine 1664 16 part1664_16 part1680_16) (combine 1696 16 part1696_16 part1712_16)) (combine 1728 32 (combine 1728 16 part1728_16 part1744_16) (combine 1760 16 part1760_16 part1776_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part1792_16 : Interval 1792 16 := by decide +kernel
private theorem part1808_16 : Interval 1808 16 := by decide +kernel
private theorem part1824_16 : Interval 1824 16 := by decide +kernel
private theorem part1840_16 : Interval 1840 16 := by decide +kernel
private theorem part1856_16 : Interval 1856 16 := by decide +kernel
private theorem part1872_16 : Interval 1872 16 := by decide +kernel
private theorem part1888_16 : Interval 1888 16 := by decide +kernel
private theorem part1904_16 : Interval 1904 16 := by decide +kernel
private theorem part1920_16 : Interval 1920 16 := by decide +kernel
private theorem part1936_16 : Interval 1936 16 := by decide +kernel
private theorem part1952_16 : Interval 1952 16 := by decide +kernel
private theorem part1968_16 : Interval 1968 16 := by decide +kernel
private theorem part1984_16 : Interval 1984 16 := by decide +kernel
private theorem part2000_16 : Interval 2000 16 := by decide +kernel
private theorem part2016_16 : Interval 2016 16 := by decide +kernel
private theorem part2032_16 : Interval 2032 16 := by decide +kernel
theorem part1792_256 : Interval 1792 256 := (combine 1792 128 (combine 1792 64 (combine 1792 32 (combine 1792 16 part1792_16 part1808_16) (combine 1824 16 part1824_16 part1840_16)) (combine 1856 32 (combine 1856 16 part1856_16 part1872_16) (combine 1888 16 part1888_16 part1904_16))) (combine 1920 64 (combine 1920 32 (combine 1920 16 part1920_16 part1936_16) (combine 1952 16 part1952_16 part1968_16)) (combine 1984 32 (combine 1984 16 part1984_16 part2000_16) (combine 2016 16 part2016_16 part2032_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part2048_16 : Interval 2048 16 := by decide +kernel
private theorem part2064_16 : Interval 2064 16 := by decide +kernel
private theorem part2080_16 : Interval 2080 16 := by decide +kernel
private theorem part2096_16 : Interval 2096 16 := by decide +kernel
private theorem part2112_16 : Interval 2112 16 := by decide +kernel
private theorem part2128_16 : Interval 2128 16 := by decide +kernel
private theorem part2144_16 : Interval 2144 16 := by decide +kernel
private theorem part2160_16 : Interval 2160 16 := by decide +kernel
private theorem part2176_16 : Interval 2176 16 := by decide +kernel
private theorem part2192_16 : Interval 2192 16 := by decide +kernel
private theorem part2208_16 : Interval 2208 16 := by decide +kernel
private theorem part2224_16 : Interval 2224 16 := by decide +kernel
private theorem part2240_16 : Interval 2240 16 := by decide +kernel
private theorem part2256_16 : Interval 2256 16 := by decide +kernel
private theorem part2272_16 : Interval 2272 16 := by decide +kernel
private theorem part2288_16 : Interval 2288 16 := by decide +kernel
theorem part2048_256 : Interval 2048 256 := (combine 2048 128 (combine 2048 64 (combine 2048 32 (combine 2048 16 part2048_16 part2064_16) (combine 2080 16 part2080_16 part2096_16)) (combine 2112 32 (combine 2112 16 part2112_16 part2128_16) (combine 2144 16 part2144_16 part2160_16))) (combine 2176 64 (combine 2176 32 (combine 2176 16 part2176_16 part2192_16) (combine 2208 16 part2208_16 part2224_16)) (combine 2240 32 (combine 2240 16 part2240_16 part2256_16) (combine 2272 16 part2272_16 part2288_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part2304_16 : Interval 2304 16 := by decide +kernel
private theorem part2320_16 : Interval 2320 16 := by decide +kernel
private theorem part2336_16 : Interval 2336 16 := by decide +kernel
private theorem part2352_16 : Interval 2352 16 := by decide +kernel
private theorem part2368_16 : Interval 2368 16 := by decide +kernel
private theorem part2384_16 : Interval 2384 16 := by decide +kernel
private theorem part2400_16 : Interval 2400 16 := by decide +kernel
private theorem part2416_16 : Interval 2416 16 := by decide +kernel
private theorem part2432_16 : Interval 2432 16 := by decide +kernel
private theorem part2448_16 : Interval 2448 16 := by decide +kernel
private theorem part2464_16 : Interval 2464 16 := by decide +kernel
private theorem part2480_16 : Interval 2480 16 := by decide +kernel
private theorem part2496_16 : Interval 2496 16 := by decide +kernel
private theorem part2512_16 : Interval 2512 16 := by decide +kernel
private theorem part2528_16 : Interval 2528 16 := by decide +kernel
private theorem part2544_16 : Interval 2544 16 := by decide +kernel
theorem part2304_256 : Interval 2304 256 := (combine 2304 128 (combine 2304 64 (combine 2304 32 (combine 2304 16 part2304_16 part2320_16) (combine 2336 16 part2336_16 part2352_16)) (combine 2368 32 (combine 2368 16 part2368_16 part2384_16) (combine 2400 16 part2400_16 part2416_16))) (combine 2432 64 (combine 2432 32 (combine 2432 16 part2432_16 part2448_16) (combine 2464 16 part2464_16 part2480_16)) (combine 2496 32 (combine 2496 16 part2496_16 part2512_16) (combine 2528 16 part2528_16 part2544_16))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave225Hit
set_option maxRecDepth 50000

def fullPrefix (inv : Bool) := ((program inv).drop (initPC inv)).take (if inv then 70 else 92)
theorem fullShape (inv : Bool) : fullPrefix inv =
    withHits 1721 1722 inv swaps ((if inv then prepareInv else prepare).map Op.enter) := by
  cases inv <;> rfl

theorem complete (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1721) (s.basis 1722) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    let out:=run (fullPrefix inv) m s
    out.phase=s.phase ∧ out.basis 1725=nearby k ∧ out.basis 1724=(crossing ports k).read v ∧
    out.basis 1596=(signExpr ports k).read v ∧ out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact assembled ports 1721 1722 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange
    (by cases inv
        · exact controlCert k
        · exact controlInvCert k)
end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave240Hit
set_option maxRecDepth 50000

def fullPrefix (inv : Bool) := ((program inv).drop (initPC inv)).take (if inv then 70 else 92)
theorem fullShape (inv : Bool) : fullPrefix inv =
    withHits 1713 1714 inv swaps ((if inv then prepareInv else prepare).map Op.enter) := by
  cases inv <;> rfl

theorem complete (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1713) (s.basis 1714) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    let out:=run (fullPrefix inv) m s
    out.phase=s.phase ∧ out.basis 1717=nearby k ∧ out.basis 1716=(crossing ports k).read v ∧
    out.basis 1596=(signExpr ports k).read v ∧ out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact assembled ports 1713 1714 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange
    (by cases inv
        · exact controlCert k
        · exact controlInvCert k)
end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave255Hit
set_option maxRecDepth 50000

def fullPrefix (inv : Bool) := ((program inv).drop (initPC inv)).take (if inv then 70 else 92)
theorem fullShape (inv : Bool) : fullPrefix inv =
    withHits 1706 1707 inv swaps ((if inv then prepareInv else prepare).map Op.enter) := by
  cases inv <;> rfl

theorem complete (inv : Bool) (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (k : Mode) (mode : k=farMode (s.basis 1706) (s.basis 1707) small)
    (a:s.basis 1559=false) (b:s.basis 1560=false)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before ports inv k q).read v)
    (exchange : right k=true → ∀i<15,i≤key k → s.basis (swaps i)=decide (i=key k)) :
    let out:=run (fullPrefix inv) m s
    out.phase=s.phase ∧ out.basis 1710=nearby k ∧ out.basis 1709=(crossing ports k).read v ∧
    out.basis 1596=(signExpr ports k).read v ∧ out.basis 1597=((crossing ports k).read v && (signExpr ports k).read v) := by
  rw [fullShape]
  have sep : ∀i : Fin 15, swaps i≠1559 ∧ swaps i≠1560 := by decide +kernel
  exact assembled ports 1706 1707 inv _ swaps sites (fun i hi=>sep ⟨i,hi⟩) s m v small
    (by decide) (by decide) a b k mode input exchange
    (by cases inv
        · exact controlCert k
        · exact controlInvCert k)
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end


section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 224) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 224 q∈(W.compactSkywalkTickLayout base 225).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small:min z.u z.v<2^144) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 224) raw
    PackedCut loPairs hiPairs 240 1723 1721 1722 (negative sg z.u)
      (decide (3*2^160≤z.u+z.v)) (decide (3*2^160≤z.u+z.v ∧ 2^144≤z.u))
      origin (run Partial.portal225 m origin) := by
  let origin:=pullState (OB5.sig 224) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^160≤z.u+z.v)
  let long:=decide (3*2^160≤z.u+z.v ∧ 2^144≤z.u)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1723=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 224 1723)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1721 far) 1722 long⟩:=flags_values v t1 _ _ sg small vs left right
  have keep (q:Wire) (qf:q≠1721) (qu:q≠1722):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg small cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 497 1042 240 1723 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 497 ^^ origin.basis 1042)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 240 1723 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 240 1723 1721 1722 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
theorem physical_frame_for (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 225 raw.basis)
    (route sg:Bool)
    (record:let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
      SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    PackedCut loPairs hiPairs 240 1723 1721 1722 (negative sg z.u)
      (decide (3*2^160≤z.u+z.v)) (decide (3*2^160≤z.u+z.v ∧ 2^144≤z.u))
      origin (run Partial.portal225 m origin) := by
  have _input:=original_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact physical_frame_local _ (true_small seed p 225 (by omega) hp (by decide)) raw m route sg record
theorem physical_frame (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    ∃sg:Bool,PackedCut loPairs hiPairs 240 1723 1721 1722 (negative sg z.u)
      (decide (3*2^160≤z.u+z.v)) (decide (3*2^160≤z.u+z.v ∧ 2^144≤z.u))
      origin (run Partial.portal225 m origin) := by
  obtain ⟨route,sg,input⟩:=real_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact ⟨sg,physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m h route sg input⟩
#print axioms physical_frame
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 269) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 269 q∈(W.compactSkywalkTickLayout base 270).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small:min z.u z.v<2^121) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 269) raw
    PackedCut loPairs hiPairs 285 1700 1698 1699 (negative sg z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u))
      origin (run Partial.portal270 m origin) := by
  let origin:=pullState (OB5.sig 269) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (3*2^137≤z.u+z.v)
  let long:=decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1700=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 269 1700)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1698 far) 1699 long⟩:=flags_values v t1 _ _ sg small vs left right
  have keep (q:Wire) (qf:q≠1698) (qu:q≠1699):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg small cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 528 1028 285 1700 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 528 ^^ origin.basis 1028)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 285 1700 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 285 1700 1698 1699 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
theorem physical_frame_for (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 270 raw.basis)
    (route sg:Bool)
    (record:let z:=SkywalkNat.step^[270] (SkywalkNat.init seed p)
      SkywalkIntegerInput (W.compactSkywalkTickLayout base 270) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let z:=SkywalkNat.step^[270] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 269) raw
    PackedCut loPairs hiPairs 285 1700 1698 1699 (negative sg z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u))
      origin (run Partial.portal270 m origin) := by
  have _input:=original_input d seed p 270 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact physical_frame_local _ (true_small seed p 270 (by omega) hp (by decide)) raw m route sg record
theorem physical_frame (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 270 raw.basis) :
    let z:=SkywalkNat.step^[270] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 269) raw
    ∃sg:Bool,PackedCut loPairs hiPairs 285 1700 1698 1699 (negative sg z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u))
      origin (run Partial.portal270 m origin) := by
  obtain ⟨route,sg,input⟩:=real_input d seed p 270 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact ⟨sg,physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m h route sg input⟩
#print axioms physical_frame
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem allRows : Interval 0 4096 := (combine 0 2048 (combine 0 1024 (combine 0 512 (combine 0 256 part0_256 part256_256) (combine 512 256 part512_256 part768_256)) (combine 1024 512 (combine 1024 256 part1024_256 part1280_256) (combine 1536 256 part1536_256 part1792_256))) (combine 2048 1024 (combine 2048 512 (combine 2048 256 part2048_256 part2304_256) (combine 2560 256 part2560_256 part2816_256)) (combine 3072 512 (combine 3072 256 part3072_256 part3328_256) (combine 3584 256 part3584_256 part3840_256))))
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify ArchiveFieldScratch StairArchiveHandoff
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 8192

def step (inv:Bool) := if inv then backward else forward
def source (inv:Bool) := if inv then output else input
def destination (inv:Bool) := if inv then input else output
def initial (inv:Bool) (r:Nat) := if inv then result r else r
def finalValue (inv:Bool) (r:Nat) := if inv then r else result r

private theorem width_bound (inv:Bool) : wires (step inv) ⊆ Finset.range width := by
  apply bounded
  cases inv <;> decide +kernel

private theorem lookup (inv : Bool) (r : Fin 4096) (q:Fin width) :
    (get (source inv) q).testBit r=(initial inv r).testBit q ∧
    (get (destination inv) q).testBit r=(finalValue inv r).testBit q := by
  have h:=allRows r q
  simp only [Nat.zero_add] at h
  cases inv
  · exact h
  · exact ⟨h.2,h.1⟩

theorem apply_guard (f:Wire→Wire) (inv:Bool) (r:Fin 4096)
    (inj:∀a b : Fin width, f a=f b → a=b) (m:List Bool) (s:State)
    (entry:∀q∈wires (step inv),s.basis (f q)=(initial inv r).testBit q) :
    (run (renameProgram f (step inv)) m s).phase=s.phase ∧
    (∀q∈wires (step inv),(run (renameProgram f (step inv)) m s).basis (f q)=(finalValue inv r).testBit q) ∧
    ∀q∉wires (renameProgram f (step inv)),(run (renameProgram f (step inv)) m s).basis q=s.basis q := by
  have targetOK:∀g∈step inv,target g < (source inv).length := by cases inv <;> decide +kernel
  have active:mask.testBit r=true := by
    change (2^4096-1:Nat).testBit r=true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true r.isLt
  let v:=value (source inv) r
  have rel:Rel (source inv) v r:=value_rel _ _
  have bound:=width_bound inv
  have finInj:∀a∈Finset.range width,∀b∈Finset.range width,f a=f b → a=b := by
    intro a ha b hb eq
    exact congrArg Fin.val (inj ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ eq)
  have data:∀q∈wires (step inv),(pullState f s).basis q=v.testBit q := by
    intro q h
    exact ((entry q h).trans (lookup inv r ⟨q,Finset.mem_range.mp (bound h)⟩).1.symm).trans (rel q).symm
  have checked:eval mask (step inv) (source inv)=(true,destination inv) := by
    cases inv
    · exact forward_checked
    · exact backward_checked
  have logical:=StairArchiveRows.run_row (step inv) mask r v m (pullState f s)
    (source inv) (destination inv) active targetOK rel checked data
  have phys:=run_rename_pool f _ finInj _ bound m (pullState f s) s rfl (fun _ _=>rfl)
  exact ⟨phys.1.trans logical.1,
    fun q h=>((phys.2 q (bound h)).trans (logical.2.1 q h)).trans (lookup inv r ⟨q,Finset.mem_range.mp (bound h)⟩).2,
    fun q h=>run_preserves_outside _ _ _ q h⟩
#print axioms apply_guard
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave225Hit
set_option maxRecDepth 50000

def fullPostfix (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 92 else 70)
theorem postfixShape (inv : Bool) : fullPostfix inv = afterWord inv ++
    (dropAll 1560 swaps LeaveSelector.tags 0 15 ++ (flagOps 1721 1722 (!inv)).reverse.map Op.exit) := by
  cases inv <;> rfl

theorem retiredFull (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v)
    (l : left k=(v 1721 && v 1722)) (r : right k=(v 1721 && !v 1722))
    (exchange : right k=true → ∀i<15,i≤key k → v (swaps i)=decide (i=key k)) :
    run (fullPostfix inv) m s=⟨s.phase,clearKey (fun q=>(restored ports inv k q).read v)⟩ := by
  have ws : ∀iv : Bool, ∀k : Mode,witnesses 1721 1722 swaps k (restored ports iv k) := by decide +kernel
  rw [postfixShape]
  exact full_release 1721 1722 swaps sites separate (by decide) (by decide) (!inv) k s m v _ _
    (clear inv k s m v input) (ws inv k) l r exchange

#print axioms retiredFull
#print axioms complete
end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave240Hit
set_option maxRecDepth 50000

def fullPostfix (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 92 else 70)
theorem postfixShape (inv : Bool) : fullPostfix inv = afterWord inv ++
    (dropAll 1560 swaps LeaveSelector.tags 0 15 ++ (flagOps 1713 1714 (!inv)).reverse.map Op.exit) := by
  cases inv <;> rfl

theorem retiredFull (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v)
    (l : left k=(v 1713 && v 1714)) (r : right k=(v 1713 && !v 1714))
    (exchange : right k=true → ∀i<15,i≤key k → v (swaps i)=decide (i=key k)) :
    run (fullPostfix inv) m s=⟨s.phase,clearKey (fun q=>(restored ports inv k q).read v)⟩ := by
  have ws : ∀iv : Bool, ∀k : Mode,witnesses 1713 1714 swaps k (restored ports iv k) := by decide +kernel
  rw [postfixShape]
  exact full_release 1713 1714 swaps sites separate (by decide) (by decide) (!inv) k s m v _ _
    (clear inv k s m v input) (ws inv k) l r exchange

#print axioms retiredFull
#print axioms complete
end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave255Hit
set_option maxRecDepth 50000

def fullPostfix (inv : Bool) := ((program inv).drop (retirePC inv)).take (if inv then 92 else 70)
theorem postfixShape (inv : Bool) : fullPostfix inv = afterWord inv ++
    (dropAll 1560 swaps LeaveSelector.tags 0 15 ++ (flagOps 1706 1707 (!inv)).reverse.map Op.exit) := by
  cases inv <;> rfl

theorem retiredFull (inv : Bool) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀q,s.basis q=(post ports prepare inv k q).read v)
    (l : left k=(v 1706 && v 1707)) (r : right k=(v 1706 && !v 1707))
    (exchange : right k=true → ∀i<15,i≤key k → v (swaps i)=decide (i=key k)) :
    run (fullPostfix inv) m s=⟨s.phase,clearKey (fun q=>(restored ports inv k q).read v)⟩ := by
  have ws : ∀iv : Bool, ∀k : Mode,witnesses 1706 1707 swaps k (restored ports iv k) := by decide +kernel
  rw [postfixShape]
  exact full_release 1706 1707 swaps sites separate (by decide) (by decide) (!inv) k s m v _ _
    (clear inv k s m v input) (ws inv k) l r exchange

#print axioms retiredFull
#print axioms complete
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

/-- A nibble of the signed rail is encoded by the one's complement of its
magnitude whenever the full signed rail is negative. -/
def signedNibble (n:Bool) (m:Nat) := m ^^^ (if n then 15 else 0)

def encodedPair (g neg:Bool) (a m:Nat) := if g then signedNibble neg m+16*a else a+16*signedNibble neg m

def rowOf (a m:Nat) (g neg f u:Bool) :=
  encodedPair g neg a m + 256*g.toNat+512*neg.toNat+1024*f.toNat+2048*u.toNat

def borrow (a m:Nat) (u:Bool) := (u && m.testBit 0 && !a.testBit 0).toNat
def updateA (a:Nat) (f:Bool) := 2*(if f then 2 else a/2)+a%2
def updateM (a m:Nat) (f u:Bool) := 2*EnterLimb.guardWord (m/2) (a/2) (borrow a m u) f u+m%2

def expected (a m:Nat) (g neg f u:Bool) :=
  let x:=updateA a f;let y:=updateM a m f u
  let sg:=neg ^^ x.testBit 3 ^^ (signedNibble neg y).testBit 3
  encodedPair g neg x y+256*g.toNat+512*sg.toNat+1024*f.toNat+2048*u.toNat+(if f then 4096*(a/2) else 0)

def RowSpec (x:Nat) : Prop :=
  ∀ y:Fin 16,∀g n f u:Bool,rowOf x y g n f u<4096 ∧ result (rowOf x y g n f u)=expected x y g n f u
instance (x:Nat):Decidable (RowSpec x):=inferInstanceAs (Decidable (∀_:Fin 16,∀ _ _ _ _:Bool,_))

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end




section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row0 : RowSpec 0 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row1 : RowSpec 1 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row10 : RowSpec 10 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row11 : RowSpec 11 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row12 : RowSpec 12 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row13 : RowSpec 13 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row14 : RowSpec 14 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row15 : RowSpec 15 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row2 : RowSpec 2 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row3 : RowSpec 3 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row4 : RowSpec 4 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row5 : RowSpec 5 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row6 : RowSpec 6 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row7 : RowSpec 7 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row8 : RowSpec 8 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row9 : RowSpec 9 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def nibble (W V:Nat):Nat:=(W/V)%16

theorem digit (W V:Nat):nibble W V/2=W/(2*V)%8 := by
  rw [Nat.mul_comm 2 V,←Nat.div_div_eq_div_mul]
  unfold nibble
  omega

theorem bit (W V:Nat) (pos:0<V): (nibble W V).testBit 0=true ↔ V≤W%(2*V) := by
  rw [←Nat.mod_two_eq_one_iff_testBit_zero,Nat.mul_comm 2 V,Nat.mod_mul]
  have rem:=Nat.mod_lt W pos
  change (W/V%16)%2=1 ↔ _
  by_cases b:W/V%2=1
  · rw [b,Nat.mul_one];omega
  · have z:W/V%2=0:=by omega
    rw [z,Nat.mul_zero];omega

theorem frac (W V:Nat) (pos:0<V):nibble W V%2=(W%(2*V))/V := by
  rw [Nat.mul_comm 2 V,Nat.mod_mul,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt (Nat.mod_lt _ pos)]
  unfold nibble;omega

theorem digit_join (W V:Nat):nibble W V=2*(W/(2*V)%8)+nibble W V%2 := by
  rw [←digit];omega

theorem borrowed (W M V:Nat) (pos:0<V) :
    borrow (nibble W V) (nibble M V) true=(if V≤M%(2*V) ∧ W%(2*V)<V then 1 else 0) := by
  have m:=bit M V pos
  have w:=bit W V pos
  cases hb:(nibble M V).testBit 0 <;> cases ha:(nibble W V).testBit 0 <;> simp_all [borrow]

theorem short_digits (W M V e:Nat) (pos:0<V) (ew:e≤1)
    (rel:W/(2*V)=M/(2*V)+e) (actual:e=borrow (nibble W V) (nibble M V) true)
    (df:3≤W/(2*V)) :
    let d:=(W/(2*V)-2)*(2*V)
    updateA (nibble W V) true=nibble (W-d) V ∧
    updateM (nibble W V) (nibble M V) true true=nibble (M-d) V := by
  have hh:=EnterLimb.limbs (2*V) W M e (by omega) ew true df (fun _=>rel)
  dsimp only at hh ⊢
  obtain ⟨wmod,wh,mm,mh⟩:=hh
  simp only [ite_true] at mm mh
  have p1: nibble (W-(W/(2*V)-2)*(2*V)) V%2=nibble W V%2:=by rw [frac _ _ pos,wmod,←frac _ _ pos]
  have p2: nibble (M-(W/(2*V)-2)*(2*V)) V%2=nibble M V%2:=by rw [frac _ _ pos,mm,←frac _ _ pos]
  constructor
  · rw [digit_join (W-_) V,wh,p1]
    rfl
  · rw [digit_join (M-_) V,p2,mh]
    unfold updateM
    rw [digit,digit,←actual]
    simp [EnterLimb.guardWord]

theorem short_other (W M V:Nat) (pos:0<V) (df:3≤W/(2*V)) :
    let d:=(W/(2*V)-2)*(2*V)
    updateA (nibble W V) true=nibble (W-d) V ∧
    updateM (nibble W V) (nibble M V) true false=nibble M V := by
  have hh:=EnterLimb.limbs (2*V) W M 0 (by omega) (by decide) false df (by simp)
  obtain ⟨wm,wh,_⟩:=hh
  dsimp only at wm wh ⊢
  constructor
  · rw [digit_join (W-_) V,wh,frac (W-_) _ pos,wm,←frac];rfl
    exact pos
  · unfold updateM
    simp only [borrow,Bool.false_and,Bool.toNat_false,EnterLimb.guardWord,Bool.false_eq_true,ite_false,
      Nat.add_zero,Nat.sub_zero,Nat.xor_zero,Nat.add_mod_right,Nat.mod_mod]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega

theorem near_digits (W M V:Nat) :
    updateA (nibble W V) false=nibble W V ∧
    updateM (nibble W V) (nibble M V) false false=nibble M V := by
  constructor
  · simp [updateA];omega
  · unfold updateM
    rw [EnterLimb.unchanged _ _ _ (by simp [borrow])]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega
#print axioms short_digits
#print axioms short_other
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
theorem shape (a m:Fin 16) (g n f u:Bool) : rowOf a m g n f u<4096 ∧ result (rowOf a m g n f u)=expected a m g n f u := by
  apply (show RowSpec a from ?_) m g n f u
  fin_cases a
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
#print axioms shape
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def cutUnit (b k:Nat):Nat:=2^(b+k)

theorem shadow_digits (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let X:=z.u+z.v; let e:=PortalValues.negative sg z.u; let M:=z.u-e.toNat
    let V:=cutUnit b k; let A:=nibble X V; let B:=nibble M V
    let mode:=decide (Shadow.far b k z); let long:=decide (Shadow.far b k z ∧ 2^b≤z.u)
    let T:=Shadow.reduced b k z
    let AA:=nibble (T.u+T.v) V; let BB:=nibble (T.u-e.toNat) V
    updateA A mode=AA ∧ updateM A B mode long=BB ∧ AA<8 ∧ BB<8 := by
  dsimp only
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let T:=Shadow.reduced b k z
  let e:=PortalValues.negative sg z.u
  have vn:0<V:=by simp [V,cutUnit]
  have mul:2*V=U:=by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]
  have limit:2^b≤V:=by unfold V cutUnit;apply Nat.pow_le_pow_right (by decide);omega
  have eu:e.toNat≤z.u:=by
    by_cases pos:0<z.u <;> cases sg <;> simp_all [e,PortalValues.negative];omega
  obtain ⟨tu,tx,hi,_sign,_tm⟩:=Shadow.reduced_values b k z sg small
  change T.u+T.v<3*U at hi
  have less (n:Nat) (h:n≤T.u+T.v):nibble n V<8:=by
    have div:n/V<8:=(Nat.div_lt_iff_lt_mul vn).mpr (by rw [←mul] at hi; omega)
    exact (Nat.mod_le _ _).trans_lt div
  have bound2:=less (T.u-e.toNat) (by omega)
  suffices parts:updateA (nibble (z.u+z.v) V) (decide (Shadow.far b k z))=nibble (T.u+T.v) V ∧
      updateM (nibble (z.u+z.v) V) (nibble (z.u-e.toNat) V) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u))=nibble (T.u-e.toNat) V by
    exact ⟨parts.1,parts.2,less _ (le_refl _),bound2⟩
  dsimp only [T]
  by_cases hf:Shadow.far b k z
  · have h:3≤(z.u+z.v)/(2*V):=mul ▸ hf
    have gap:Shadow.gap b k z=((z.u+z.v)/(2*V)-2)*(2*V):=by rw [mul];rfl
    by_cases hl:2^b≤z.u
    · let X:=z.u+z.v;let M:=z.u-e.toNat
      let w:=borrow (nibble X V) (nibble M V) true
      have bw:w≤1:=by unfold w borrow;cases _ && _ && _ <;> decide
      have rel:X/(2*V)=M/(2*V)+w:=by
        rw [show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        have add:z.v+e.toNat≤V := by
          change z.v+e.toNat≤V
          have hv:z.v<2^b:=by omega
          have ee:e.toNat≤1:=by cases e <;> decide
          omega
        have hh:=half_limb_borrow V M (z.v+e.toNat) vn add
        change (M+(z.v+e.toNat))/(2*V)=M/(2*V)+_ at hh
        change _=M/(2*V)+borrow (nibble X V) (nibble M V) true
        rw [borrowed _ _ _ vn,show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        exact hh
      have frame:=short_digits X M V w vn bw rel rfl h
      simp only [hf,hl,true_and,decide_true,ite_true] at tu tx _tm ⊢
      rw [gap] at tu tx _tm
      rw [_sign] at _tm
      change T.u+T.v=_ at tx
      change T.u-e.toNat=_ at _tm
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble q V) _tm.symm)⟩
    · have frame:=short_other (z.u+z.v) (z.u-e.toNat) V vn h
      simp only [hf,hl,true_and,decide_false,decide_true,ite_true] at tu tx ⊢
      rw [gap] at tx
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble (q-e.toNat) V) tu.symm)⟩
  · have dst:Shadow.reduced b k z=z:=by simp [Shadow.reduced,hf]
    simp only [hf,false_and,decide_false,dst]
    exact near_digits (z.u+z.v) (z.u-e.toNat) V
#print axioms shadow_digits
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def initialRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
  rowOf (nibble (z.u+z.v) V) (nibble (z.u-e.toNat) V) g e
    (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u))

def shadowRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  let T:=Shadow.reduced b k z; let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
  encodedPair g e (nibble (T.u+T.v) V) (nibble (T.u-e.toNat) V)+256*g.toNat+
    1024*(decide (Shadow.far b k z)).toNat+2048*(decide (Shadow.far b k z ∧ 2^b≤z.u)).toNat+
    (if Shadow.far b k z then 4096*(Shadow.high b k z%8) else 0)

theorem rows (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) (small:min z.u z.v<2^b) :
    initialRow b k z g sg<4096 ∧ result (initialRow b k z g sg)=shadowRow b k z g sg := by
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let e:=PortalValues.negative sg z.u
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let T:=Shadow.reduced b k z
  let A:=nibble (z.u+z.v) V;let M:=nibble (z.u-e.toNat) V
  let A':=nibble (T.u+T.v) V;let M':=nibble (T.u-e.toNat) V
  have sh:=shape ⟨A,Nat.mod_lt _ (by decide)⟩ ⟨M,Nat.mod_lt _ (by decide)⟩ g e f u
  refine ⟨sh.1,sh.2.trans ?_⟩
  obtain ⟨dA,dM,a0,m0⟩:=shadow_digits b k z sg small
  change updateA A f=A' at dA
  change updateM A M f u=M' at dM
  change A'<8 at a0;change M'<8 at m0
  have top (j:Nat) (h:j<8):j.testBit 3=false:=Nat.testBit_lt_two_pow (by simpa only [show 2^3=8 by decide] using h)
  have signedTop : (signedNibble e M').testBit 3=e:=by
    cases e <;> simp [signedNibble,Nat.testBit_xor,top _ m0,show Nat.testBit 15 3=true by decide]
  have head:A/2=Shadow.high b k z%8:=by
    rw [show A=nibble (z.u+z.v) V by rfl,digit,show 2*V=U by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]]
    rfl
  change expected A M g e f u=_
  unfold expected
  rw [dA,dM]
  dsimp only
  rw [top _ a0,signedTop,head]
  simp [shadowRow,f,u,e,T,V,A',M']
#print axioms rows
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open EnterProof

theorem actual_residue (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let T:=reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V := by
  let V:=cutUnit b k
  let T:=reduced b k z
  let e:=PortalValues.negative sg z.u
  obtain ⟨tu,tx,hi,sign,tm⟩:=reduced_values b k z sg small
  rw [sign] at tm
  have scale:limb b k=2*V:=by simp [limb,cutUnit,V,pow_succ,Nat.mul_comm]
  have periodic (N d:Nat) (eq:N≥d) (mul:V∣d):(N-d)%V=N%V:=by
    obtain ⟨j,rfl⟩:=mul
    conv_rhs => rw [show N=N-V*j+V*j by omega,Nat.add_mul_mod_self_left]
  have dep:V∣gap b k z := by
    unfold gap;rw [scale]
    exact ⟨(high b k z-2)*2,by ring⟩
  change (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V
  have pos:0<V:=by simp [V,cutUnit]
  by_cases hf:far b k z
  · obtain ⟨_,bound,_⟩:=represented _ _ _ small hf
    change 2*limb b k≤T.u+T.v at bound
    simp only [hf,ite_true,true_and] at tx tm tu
    have light:2^b≤limb b k:=by unfold limb;apply Nat.pow_le_pow_right (by decide);omega
    change T.u+T.v=z.u+z.v-gap b k z at tx
    have enough:gap b k z≤z.u+z.v:=by omega
    rw [tx,periodic _ _ enough dep]
    refine ⟨rfl,?_⟩
    by_cases hl:2^b≤z.u
    · simp only [hl,decide_true,ite_true] at tm tu
      have tv:T.v=z.v:=by simp [T,reduced,hf,hl]
      have sm:z.v<2^b:=by omega
      have boundU:0<T.u:=by omega
      have nne:z.u≥gap b k z+1:=by change T.u=z.u-gap b k z at tu;omega
      have eBound:e.toNat≤1:=by cases e <;> decide
      change T.u-e.toNat=z.u-e.toNat-gap b k z at tm
      rw [tm]
      exact periodic _ _ (by change gap b k z≤z.u-e.toNat;omega) dep
    · simp only [hl,decide_false] at tm
      change T.u-e.toNat=z.u-e.toNat at tm
      rw [tm]
  · simp [T,reduced,hf]
#print axioms actual_residue
end ECDSAAdd.Entrant.StairPacket.Shadow

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 10000

def rowBefore (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then shadowRow b k z g s else initialRow b k z g s

def rowAfter (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then initialRow b k z g s else shadowRow b k z g s

theorem actual_shadow (map:Wire→Wire) (P:Program) (inv:Bool) (b k:Nat) (z:SkywalkNat.State)
    (g s:Bool) (small:min z.u z.v<2^b)
    (injective:∀a c:Fin width,map a=map c→a=c) (emitted:P=renameProgram map (step inv))
    (origin:State) (tape:List Bool)
    (data:∀q∈wires (step inv),origin.basis (map q)=(rowBefore inv b k z g s).testBit q) :
    (run P tape origin).phase=origin.phase ∧
    (∀q∈wires (step inv),(run P tape origin).basis (map q)=(rowAfter inv b k z g s).testBit q) ∧
    ∀q∉wires P,(run P tape origin).basis q=origin.basis q := by
  have h:=rows b k z g s small
  let row:Fin 4096:=⟨initialRow b k z g s,h.1⟩
  have each (q:Wire) (hq:q∈wires (step inv)):origin.basis (map q)=(initial inv row).testBit q:=by
    cases inv <;> simpa [initial,row,h.2,rowBefore] using data q hq
  rw [emitted]
  have act:=apply_guard map inv row injective tape origin each
  refine ⟨act.1,?_,act.2.2⟩
  intro q hq
  have value:=act.2.1 q hq
  cases inv <;> simpa [finalValue,row,h.2,rowAfter] using value

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic

theorem bitAt (r:List Wire) (s:BasisState) (i:Nat) (h:i<r.length):
    s (r.getD i 0)=(regValue r s).testBit i := by
  have v:=regValue_bit r i 0 s h
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases b:s (r.getD i 0) <;> simp only [b,Bool.toNat_false,Bool.toNat_true] at v ⊢ <;> simp [←v]

theorem takeValue (r:List Wire) (n:Nat) (bound:n≤r.length) (s:BasisState) :
    regValue (r.take n) s=regValue r s%2^n := by
  have h:=regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left bound] at h
  rw [h,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by simpa only [List.length_take,Nat.min_eq_left bound] using regValue_lt (r.take n) s)).symm

theorem slice_value (r:List Wire) (k:Nat) (hi:k+4≤r.length) (s:BasisState) :
    regValue ((r.drop k).take 4) s=nibble (regValue r s) (2^k) := by
  rw [takeValue _ _ (by simp;omega),PortalValues.shiftedValue _ _ (by omega)]
  rfl

private theorem nibble_inverse : ∀x:Fin 16,(15-x.val) ^^^ 15=x.val := by decide +kernel

theorem sign_digits (r:List Wire) (size:r.length=4) (s:BasisState) (neg:Bool) :
    regValue r s=signedNibble neg (regValue r (fun q=>s q ^^ neg)) := by
  cases neg
  · simp [signedNibble]
  · simp only [Bool.xor_true,regValue_complement,size,signedNibble,ite_true]
    exact (nibble_inverse ⟨regValue r s,by simpa [size] using regValue_lt r s⟩).symm

structure Ports (A B:List Wire) (g n f u:Wire) (rs:List Wire) where
  a : A.length=4
  b : B.length=4
  clear : List Wire
  list : rs=A++B++[g,n,f,u]++clear

theorem read_ports {A B g n f u rs} (ports:Ports A B g n f u rs) (z:SkywalkNat.State) (k b:Nat) (G S:Bool) (s:BasisState)
    (G0:s g=G) (N:s n=PortalValues.negative S z.u)
    (F:s f=decide (Shadow.far b k z)) (U:s u=decide (Shadow.far b k z ∧ 2^b≤z.u))
    (zero:∀q∈ports.clear,s q=false)
    (x:regValue (if G then B else A) s=nibble (z.u+z.v) (cutUnit b k))
    (y:regValue (if G then A else B) (fun q=>s q ^^ PortalValues.negative S z.u)=
      nibble (z.u-(PortalValues.negative S z.u).toNat) (cutUnit b k)) :
    regValue rs s=initialRow b k z G S := by
  have h0:regValue ports.clear s=0:=(regValue_zero _ _).mpr zero
  have controlValue:regValue [g,n,f,u] s=(s g).toNat+2*((s n).toNat+2*((s f).toNat+2*(s u).toNat)):=by
    simp [regValue,Bool.toNat]
    cases s g <;> cases s n <;> cases s f <;> cases s u <;> rfl
  rw [ports.list,regValue_append,regValue_append,regValue_append,h0,Nat.mul_zero,Nat.add_zero,
    List.length_append,ports.a,ports.b,controlValue,G0,N,F,U]
  cases G <;> simp only [Bool.false_eq_true,ite_false,ite_true] at x y
  · have y0:=sign_digits B ports.b s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,Bool.false_eq_true,ite_false,Bool.toNat_false];omega
  · have y0:=sign_digits A ports.a s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,ite_true,Bool.toNat_true];omega
#print axioms read_ports
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic
set_option maxRecDepth 16000

theorem value_of_bits (r:List Wire) (s:BasisState) (W:Nat)
    (h:∀i<r.length,s (r.getD i 0)=W.testBit i):regValue r s=W%2^r.length := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases low:i<r.length
  · rw [←bitAt r s i low,h i low,Nat.testBit_mod_two_pow]
    simp [low]
  · rw [Nat.testBit_mod_two_pow,Nat.testBit_lt_two_pow (lt_of_lt_of_le (regValue_lt r s)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [low]

theorem forward_all : wires forward=Finset.range width:=by decide +kernel

def leftWord (g e:Bool) (A M:Nat) := if g then signedNibble e M else A
def rightWord (g e:Bool) (A M:Nat) := if g then A else signedNibble e M

private theorem signedSmall (e:Bool) (M:Fin 16) : signedNibble e M<16 := by
  have t:∀b:Bool,∀m:Fin 16,signedNibble b m<16:=by decide +kernel
  exact t e M

theorem projected (b k:Nat) (z:SkywalkNat.State) (G S:Bool) :
    let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
    let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V;let W:=shadowRow b k z G S
    W%16=leftWord G e A M ∧ (W/16)%16=rightWord G e A M ∧ W/32768=0 := by
  dsimp only
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
  let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
  have ar:A<16:=Nat.mod_lt _ (by decide)
  have mr:M<16:=Nat.mod_lt _ (by decide)
  have sn:signedNibble e M<16:=signedSmall e ⟨M,mr⟩
  have gr:G.toNat≤1:=by cases G <;> decide
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  have fb:f.toNat≤1:=by cases f <;> decide
  have ub:u.toNat≤1:=by cases u <;> decide
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  have hh:h<8:=by dsimp [h];split <;> omega
  let X:=encodedPair G e A M+256*G.toNat+1024*f.toNat+2048*u.toNat+4096*h
  have val:shadowRow b k z G S=X:=by
    unfold shadowRow X h
    by_cases off:Shadow.far b k z <;> simp [off,T,V,e,A,M,f,u]
  rw [val]
  change X%16=leftWord G e A M ∧ X/16%16=rightWord G e A M ∧ X/32768=0
  dsimp only [X,encodedPair,leftWord,rightWord]
  cases G <;> simp only [ite_true,Bool.false_eq_true,ite_false,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem output_values (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (plen:ports.length=width)
    (data:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
    let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
    regValue (ports.take 4) s=leftWord G e A M ∧
    regValue ((ports.drop 4).take 4) s=rightWord G e A M ∧ regValue (ports.drop 15) s=0 := by
  let W:=shadowRow b k z G S
  have p:=projected b k z G S
  have N:ports.length=23:=plen
  have whole:=value_of_bits ports s W (fun q h=>data q (forward_all ▸ Finset.mem_range.mpr (plen ▸ h)))
  rw [N,Nat.mod_eq_of_lt (show W<2^23 by have h:W/32768=0:=p.2.2;omega)] at whole
  rw [takeValue _ _ (by omega),whole,takeValue _ _ (by simp [N]),
    PortalValues.shiftedValue _ 4 (by omega),whole,PortalValues.shiftedValue _ 15 (by omega),whole]
  exact p
#print axioms output_values
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic RailPair

theorem PackedCut.unchanged {lo hi g n f u neg far long orig result}
    (P:PackedCut lo hi g n f u neg far long orig result) (q:Wire) (qn:q≠n) (qf:q≠f) (qu:q≠u)
    (qh:q∉sites hi) : result.basis q=orig.basis q:=by
  by_cases l:q∈sites lo
  · obtain ⟨p,hp,e⟩:=List.mem_flatMap.mp l
    rcases List.mem_cons.mp e with rfl|tail
    · exact (P.low p hp).1
    · obtain rfl:=List.mem_singleton.mp tail
      exact (P.low p hp).2
  · exact P.frame q qn qf qu l qh

namespace EnterProof
structure Aperture (lo hi:List (Wire×Wire)) (g n f u:Wire) (ports:List Wire) (L:SkywalkIntegerLayout)
    (net:Wire→Wire) (cut:Nat) where
  a : List Wire
  b : List Wire
  spec : Ports a b g n f u ports
  g0 : net g=L.previous
  xa : a.map net=(L.a.drop cut).take 4
  xb : b.map net=(L.b.drop cut).take 4
  na : cut+4≤L.a.length
  nb : cut+4≤L.b.length
  protected0 : ∀q∈g::(a++b++spec.clear),q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  temps : ∀q∈spec.clear,net q∈L.carry

theorem read_packed {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k))
    (raw result:State) (z:SkywalkNat.State) (G S:Bool)
    (P:PackedCut lo hi g n f u (PortalValues.negative S z.u)
      (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) result)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue rs result.basis=initialRow b k z G S:=by
  let neg:=PortalValues.negative S z.u
  have eq (q:Wire) (hq:q∈g::(A.a++A.b++A.spec.clear)):result.basis q=raw.basis (net q):=by
    obtain ⟨h0,h1,h2,hi⟩:=A.protected0 _ hq
    exact P.unchanged q h0 h1 h2 hi
  have math:=PortalValues.mathematical _ _ _ _ _ _ input
  have gOk:result.basis g=G:=(eq _ (by simp)).trans ((congrArg raw.basis A.g0).trans math.1)
  have clean:∀q∈A.spec.clear,result.basis q=false:=fun q h=>(eq _ (by simp [h])).trans
    ((regValue_zero _ _).mp input.2.2.2.2.2 _ (A.temps _ h))
  have view (ns full:List Wire) (ok:∀q∈ns,q∈g::(A.a++A.b++A.spec.clear))
      (shape:ns.map net=(full.drop (b+k)).take 4) (sz:b+k+4≤full.length) (flip:Bool) :
      regValue ns (fun q=>result.basis q ^^ flip)=nibble (regValue full (fun q=>raw.basis q ^^ flip)) (cutUnit b k) := by
    calc
      _=regValue ns (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (eq q (ok q h)))
      _=regValue (ns.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net ns (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,slice_value _ _ sz];rfl
  have left (s:Bool):=view A.a L.a (by intro q h;simp [h]) A.xa A.na s
  have right (s:Bool):=view A.b L.b (by intro q h;simp [h]) A.xb A.nb s
  apply read_ports A.spec z k b G S result.basis gOk P.sign P.mode P.orientation clean
  · cases G
    · exact (by simpa using left false : regValue A.a result.basis=_).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.1)
    · exact (by simpa using right false : regValue A.b result.basis=_).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.1)
  · cases G
    · exact (right neg).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.2)
    · exact (left neg).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.2)
#print axioms read_packed
end EnterProof
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic

theorem join (lo hi:List Wire) (cut W:Nat) (s:BasisState) (size:lo.length=cut)
    (low:regValue lo s=W%2^cut) (high:regValue hi s=nibble W (2^cut)) (bound:W/(2^cut)<16) :
    regValue (lo++hi) s=W := by
  rw [regValue_append,size,low,high,nibble,Nat.mod_eq_of_lt bound,Nat.mod_add_div]

theorem norm_nibble (r:List Wire) (size:r.length=4) (s:BasisState) (e:Bool) (Y:Nat)
    (v:regValue r s=signedNibble e Y) : regValue r (fun q=>s q ^^ e)=Y := by
  have eq: signedNibble e (regValue r (fun q=>s q ^^ e))=signedNibble e Y:=(sign_digits _ size s e).symm.trans v
  exact Nat.xor_left_inj.mp eq

theorem ordinary (rs:List Wire) (bit:Nat) (length:rs.length=bit+1) (s:BasisState) (N:Nat)
    (low:N<2^bit) (value:regValue rs s=N) : signedRegValue rs s=N:=by
  simp [signedRegValue,signedDecode,length,value,low]

theorem signed (rs:List Wire) (bit:Nat) (length:rs.length=bit+1) (s:BasisState) (u:Nat) (sg:Bool)
    (small:u<2^bit)
    (value:regValue rs (fun q=>s q ^^ PortalValues.negative sg u)=u-(PortalValues.negative sg u).toNat) :
    signedRegValue rs s=SkywalkRails.signed sg u:=by
  have lim:=regValue_lt rs s
  rw [length,pow_succ] at lim
  by_cases neg:PortalValues.negative sg u
  · have su:sg=true ∧ 0<u:=by simpa [PortalValues.negative] using neg
    rw [neg] at value
    simp only [Bool.xor_true,regValue_complement,length,pow_succ,Bool.toNat_true] at value
    unfold signedRegValue signedDecode
    simp only [length,Nat.add_sub_cancel,show ¬regValue rs s<2^bit by omega,ite_false,pow_succ,
      SkywalkRails.signed,su.1,ite_true]
    omega
  · have no:PortalValues.negative sg u=false:=by simpa using neg
    simp only [no,Bool.xor_false,Bool.toNat_false,Nat.sub_zero] at value
    rw [ordinary rs bit length _ u small value]
    cases sg
    · rfl
    · have zu:u=0:=by simp [PortalValues.negative] at no;omega
      simp [zu,SkywalkRails.signed]
#print axioms signed
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic
set_option maxRecDepth 12000

theorem tags (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :
    let W:=shadowRow b k z g s
    W.testBit 8=g ∧ W.testBit 9=false ∧ W.testBit 10=decide (Shadow.far b k z) ∧
    W.testBit 11=decide (Shadow.far b k z ∧ 2^b≤z.u) ∧ W/4096=
      (if Shadow.far b k z then Shadow.high b k z%8 else 0) := by
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative s z.u
  let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
  have ar:A<16:=Nat.mod_lt _ (by decide)
  have mr:M<16:=Nat.mod_lt _ (by decide)
  have small:∀x:Fin 16,∀n:Bool,signedNibble n x<16:=by decide +kernel
  have sn:signedNibble e M<16:=small ⟨_,mr⟩ e
  let f:=decide (Shadow.far b k z);let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  let W:=encodedPair g e A M+256*g.toNat+1024*f.toNat+2048*u.toNat+4096*h
  have w:shadowRow b k z g s=W:=by
    unfold shadowRow W h
    by_cases absent:Shadow.far b k z <;> simp [absent,T,V,e,A,M,f,u]
  have base:encodedPair g e A M<256:=by cases g <;> dsimp [encodedPair] <;> omega
  dsimp only
  rw [w]
  change W.testBit 8=g ∧ W.testBit 9=false ∧ W.testBit 10=f ∧ W.testBit 11=u ∧ W/4096=h
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  change decide (W/256%2=1)=g ∧ decide (W/512%2=1)=false ∧ decide (W/1024%2=1)=f ∧
    decide (W/2048%2=1)=u ∧ W/4096=h
  dsimp only [W]
  cases g <;> cases f <;> cases u <;> simp only [Bool.toNat_true,Bool.toNat_false,decide_eq_true_eq,decide_eq_false_iff_not] <;> omega

theorem actual_tags (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (h:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    s (ports.getD 8 0)=G ∧ s (ports.getD 9 0)=false ∧ s (ports.getD 10 0)=decide (Shadow.far b k z) ∧
    s (ports.getD 11 0)=decide (Shadow.far b k z ∧ 2^b≤z.u) := by
  rw [h 8 (by decide +kernel),h 9 (by decide +kernel),h 10 (by decide +kernel),h 11 (by decide +kernel)]
  have ⟨a,b,c,d,_⟩:=tags b k z G S
  exact ⟨a,b,c,d⟩
#print axioms actual_tags
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic RailPair
set_option maxRecDepth 12000

structure WordPlacement {lo hi g n f u rs L net b k}
    (A:Aperture lo hi g n f u rs L net (b+k)) (P:Program) where
  lowA : List Wire
  lowB : List Wire
  al : lowA.length=b+k
  bl : lowB.length=b+k
  xa : lowA.map net=L.a.take (b+k)
  xb : lowB.map net=L.b.take (b+k)
  aTop : rs.take 4=A.a
  bTop : (rs.drop 4).take 4=A.b
  protected0 : ∀q∈lowA++lowB,q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  portsCount : rs.length=width

theorem short_rails {lo hi g n f u rs L net b k} {A:Aperture lo hi g n f u rs L net (b+k)}
    (P:Program) (place:WordPlacement A P) (z:SkywalkNat.State) (G S:Bool) (small:min z.u z.v<2^b)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (outside:∀q∉wires P,post.basis q=pre.basis q) :
    let T:=Shadow.reduced b k z
    signedRegValue (place.lowA++A.a) post.basis=(SkywalkRails.encode G S T.u T.v).a ∧
    signedRegValue (place.lowB++A.b) post.basis=(SkywalkRails.encode G S T.u T.v).b := by
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
  let X:=T.u+T.v;let M:=T.u-e.toNat
  have num:=PortalValues.mathematical _ _ _ _ _ _ input
  have residue:=Shadow.actual_residue b k z S small
  obtain ⟨_,_,pos,neg,_⟩:=Shadow.reduced_values b k z S small
  change PortalValues.negative S T.u=e at neg
  change X<3*Shadow.limb b k at pos
  have limb:Shadow.limb b k=2*V:=by simp [Shadow.limb,V,cutUnit,pow_succ,Nat.mul_comm]
  rw [limb] at pos
  have pv:0<V:=by simp [V,cutUnit]
  have bounded (v:Nat) (h:v≤X):v/V<16:=(Nat.div_lt_iff_lt_mul pv).mpr (by omega)
  have Xbound:X<2^(b+k+3):=by rw [pow_add]; change X<V*8; omega
  have high:=output_values rs post.basis b k z G S place.portsCount data
  rw [place.aTop,place.bTop] at high
  have same (q:Wire) (h:q∈place.lowA++place.lowB):post.basis q=raw.basis (net q):=by
    obtain ⟨hp,hn,hf,hu,hh⟩:=place.protected0 q h
    exact (outside q hp).trans (cut.unchanged q hn hf hu hh)
  have valueLo (w full:List Wire) (sub:∀q∈w,q∈place.lowA++place.lowB)
      (shape:w.map net=full.take (b+k)) (size:b+k≤full.length) (flip:Bool) :
      regValue w (fun q=>post.basis q ^^ flip)=regValue full (fun q=>raw.basis q ^^ flip)%V:=by
    calc
      _=regValue w (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (same q (sub q h)))
      _=regValue (w.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net w (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,takeValue _ _ size];rfl
  have lowA (flag:Bool):=valueLo _ L.a (fun _ h=>List.mem_append_left _ h) place.xa (by have h:=A.na;omega) flag
  have lowB (flag:Bool):=valueLo _ L.b (fun _ h=>List.mem_append_right _ h) place.xb (by have h:=A.nb;omega) flag
  have ds:=high
  change regValue A.a post.basis=leftWord G e (nibble X V) (nibble M V) ∧
    regValue A.b post.basis=rightWord G e (nibble X V) (nibble M V) ∧ _ at ds
  have ybound:T.u≤X:=by simp [X]
  have mbound:M≤X:=Nat.le_trans (Nat.sub_le _ _) ybound
  obtain ⟨_,_,wpos,wmag⟩:=num
  change X%V=(z.u+z.v)%V ∧ M%V=(z.u-e.toNat)%V at residue
  have la:(place.lowA++A.a).length=(b+k+3)+1:=by simp [place.al,A.spec.a]
  have lb:(place.lowB++A.b).length=(b+k+3)+1:=by simp [place.bl,A.spec.b]
  cases G
  · have pl:regValue place.lowA post.basis=X%V:=by
      have v:=lowA false
      simpa only [Bool.xor_false,show regValue L.a raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowB (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowB e,show regValue L.b (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.al pl ds.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.b _ e _ ds.2.1
    have py:=join _ _ _ M _ place.bl ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨ordinary _ _ la _ X Xbound px,signed _ _ lb _ _ S (lt_of_le_of_lt ybound Xbound) py⟩
  · have pl:regValue place.lowB post.basis=X%V:=by
      have v:=lowB false
      simpa only [Bool.xor_false,show regValue L.b raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowA (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowA e,show regValue L.a (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.bl pl ds.2.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.a _ e _ ds.1
    have py:=join _ _ _ M _ place.al ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨signed _ _ la _ _ S (lt_of_le_of_lt ybound Xbound) py,ordinary _ _ lb _ X Xbound px⟩

#print axioms short_rails
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

structure FramePorts {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    (place:WordPlacement A P) (j:Fin 23) : Prop where
  a : ((ports (StairPacket.shape j) 0).a.map (windowNet j))=place.lowA++A.a
  bSites : ((ports (StairPacket.shape j) 0).b.map (windowNet j))=place.lowB++A.b
  prev : windowNet j (ports (StairPacket.shape j) 0).previous=rs.getD 8 0
  carry : ∀q∈(ports (StairPacket.shape j) 0).carry,let v:=windowNet j q
    v∈rs.drop 15 ∨ (v∉wires P ∧ net v∈L.carry ∧ v≠n ∧ v≠f ∧ v≠u ∧ v∉sites hi)
  ext : ∀r:Fin 15,let q:=windowNet j (ports (StairPacket.shape j) r).ext
    q∉wires P ∧ q∈hi.map Prod.fst
  hist : ∀r:Fin 15,let q:=windowNet j (ports (StairPacket.shape j) r).history
    q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi 

theorem complete {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    {place:WordPlacement A P} {j:Fin 23} (frame:FramePorts place j)
    (z:SkywalkNat.State) (G S:Bool) (small:min z.u z.v<2^b)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (save:∀q∉wires P,post.basis q=pre.basis q)
    (history:∀r:Fin 15,raw.basis (net (windowNet j (ports (StairPacket.shape j) r).history))=false) :
    let T:=Shadow.reduced b k z
    onRails j 0 (SkywalkRails.encode G S T.u T.v) post.basis := by
  let T:=Shadow.reduced b k z
  let Z:=SkywalkRails.encode G S T.u T.v
  have values:=short_rails P place z G S small raw pre post cut input data save
  have move (qs:List Wire):signedRegValue qs (mappedBasis j post.basis)=signedRegValue (qs.map (windowNet j)) post.basis:=by
    simp only [signedRegValue,List.length_map,PortalValues.unroute]
    rfl
  have gval:=actual_tags rs post.basis b k z G S data
  have sc:=output_values rs post.basis b k z G S place.portsCount data
  have clean:= (regValue_zero _ _).mp sc.2.2
  have retain (q:Wire) (no:q∉wires P) (n0:q≠n) (f0:q≠f) (u0:q≠u) (hi0:q∉sites hi):
      post.basis q=raw.basis (net q):=(save _ no).trans (cut.unchanged _ n0 f0 u0 hi0)
  refine ⟨(move _).trans (frame.a ▸ values.1),(move _).trans (frame.bSites ▸ values.2),?_,?_,?_⟩
  · change post.basis (windowNet j (ports (StairPacket.shape j) 0).previous)=Z.g
    rw [frame.prev,gval.1];cases G <;> rfl
  · apply (regValue_zero _ _).mpr
    intro q hq
    rcases frame.carry q hq with hs|⟨no,qc,n0,f0,u0,hi0⟩
    · exact clean _ hs
    · exact (retain _ no n0 f0 u0 hi0).trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ qc)
  · intro r _ lt
    have bound:r<15:=lt
    let i:Fin 15:=⟨r,bound⟩
    obtain ⟨no,mem⟩:=frame.ext i
    obtain ⟨p,hp,eq⟩:=List.mem_map.mp mem
    obtain ⟨nh,h0,h1,h2,hr⟩:=frame.hist i
    refine ⟨(save _ no).trans (eq ▸ (cut.upper _ hp).1),(retain _ nh h0 h1 h2 hr).trans ?_⟩
    exact history i
#print axioms complete
end ECDSAAdd.Entrant.StairPacket.EnterProof

end
