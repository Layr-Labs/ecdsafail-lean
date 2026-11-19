import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def lowerPairs : List (Wire×Wire) := Portal225Flag.loPairs
def upperPairs : List (Wire×Wire) := Portal225Flag.hiPairs
def layout : Aperture lowerPairs upperPairs 240 1723 1721 1722 ports225 (W.compactSkywalkTickLayout base 225) (OB5.sig 224) 159 where
  a:=[400, 401, 402, 403]
  b:=[945, 946, 947, 948]
  spec:=⟨by decide,by decide,[1718, 1719, 1720, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563],by decide +kernel⟩
  g0:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  na:=by decide +kernel
  nb:=by decide +kernel
  protected0:=by decide +kernel
  temps:=by decide +kernel

theorem from_full (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^144)
    (p:PackedCut lowerPairs upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u) (decide (Shadow.far 144 15 z))
        (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) (pullState (OB5.sig 224) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run Partial.enter225 m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof.forward,next.basis (map225 q)=(shadowRow 144 15 z G S).testBit q) ∧
      ∀q∉wires Partial.enter225,next.basis q=v.basis q := by
  have src:=read_packed layout raw v z G S p input
  apply actual_shadow map225 Partial.enter225 false 144 15 z G S small inc225 emitted225 v m
  intro q h
  have lim:wires EnterProof.forward ⊆ Finset.range 23 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have sz:ports225.length=23:=rfl
  have hv:=bitAt ports225 v.basis q (sz ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv
#print axioms from_full
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def lowerPairs : List (Wire×Wire) := [(408, 938), (409, 939), (410, 940)]
def upperPairs : List (Wire×Wire) := [(411, 941), (412, 942), (413, 943), (414, 944), (415, 945), (416, 946), (417, 947), (418, 948), (419, 949), (420, 950), (421, 951), (422, 952), (423, 953), (424, 954), (425, 955), (426, 956), (427, 957), (428, 958), (429, 959), (430, 960), (431, 961), (432, 962), (433, 963), (434, 964), (435, 965), (436, 966), (437, 967), (438, 968), (439, 969), (440, 970), (441, 971), (442, 972), (443, 973), (444, 974), (445, 975), (446, 976), (447, 977), (448, 978), (449, 979), (450, 980), (451, 981), (452, 982), (453, 983), (454, 984), (455, 985), (456, 986), (457, 987), (458, 988), (459, 989), (460, 990), (461, 991), (462, 992), (463, 993), (464, 994), (465, 995), (466, 996), (467, 997), (468, 998), (469, 999), (470, 1000), (471, 1001), (472, 1002), (473, 1003), (474, 1004), (475, 1005), (476, 1006), (477, 1007), (478, 1008), (479, 1009), (480, 1010), (481, 1011), (482, 1012), (483, 1013), (484, 1014), (485, 1015), (486, 1016), (487, 1017), (488, 1018), (489, 1019), (490, 1020), (491, 1021), (492, 1022), (493, 1023), (494, 1024), (495, 1025), (496, 1026), (497, 1027), (498, 1028), (499, 1029), (500, 1030), (501, 1031), (502, 1032), (503, 1033), (504, 1034), (505, 1035), (506, 1036), (507, 1037), (508, 1038), (509, 1039), (510, 1040), (511, 1041), (512, 1042)]
def layout : Aperture lowerPairs upperPairs 255 1715 1713 1714 ports240 (W.compactSkywalkTickLayout base 240) (OB5.sig 239) 151 where
  a:=[407, 408, 409, 410]
  b:=[937, 938, 939, 940]
  spec:=⟨by decide,by decide,[1710, 1711, 1712, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563],by decide +kernel⟩
  g0:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  na:=by decide +kernel
  nb:=by decide +kernel
  protected0:=by decide +kernel
  temps:=by decide +kernel

theorem from_full (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^136)
    (p:PackedCut lowerPairs upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u) (decide (Shadow.far 136 15 z))
        (decide (Shadow.far 136 15 z ∧ 2^136≤z.u)) (pullState (OB5.sig 239) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run Partial.enter240 m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof.forward,next.basis (map240 q)=(shadowRow 136 15 z G S).testBit q) ∧
      ∀q∉wires Partial.enter240,next.basis q=v.basis q := by
  have src:=read_packed layout raw v z G S p input
  apply actual_shadow map240 Partial.enter240 false 136 15 z G S small inc240 emitted240 v m
  intro q h
  have lim:wires EnterProof.forward ⊆ Finset.range 23 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have sz:ports240.length=23:=rfl
  have hv:=bitAt ports240 v.basis q (sz ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv
#print axioms from_full
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def lowerPairs : List (Wire×Wire) := [(416, 931), (417, 932), (418, 933)]
def upperPairs : List (Wire×Wire) := [(419, 934), (420, 935), (421, 936), (422, 937), (423, 938), (424, 939), (425, 940), (426, 941), (427, 942), (428, 943), (429, 944), (430, 945), (431, 946), (432, 947), (433, 948), (434, 949), (435, 950), (436, 951), (437, 952), (438, 953), (439, 954), (440, 955), (441, 956), (442, 957), (443, 958), (444, 959), (445, 960), (446, 961), (447, 962), (448, 963), (449, 964), (450, 965), (451, 966), (452, 967), (453, 968), (454, 969), (455, 970), (456, 971), (457, 972), (458, 973), (459, 974), (460, 975), (461, 976), (462, 977), (463, 978), (464, 979), (465, 980), (466, 981), (467, 982), (468, 983), (469, 984), (470, 985), (471, 986), (472, 987), (473, 988), (474, 989), (475, 990), (476, 991), (477, 992), (478, 993), (479, 994), (480, 995), (481, 996), (482, 997), (483, 998), (484, 999), (485, 1000), (486, 1001), (487, 1002), (488, 1003), (489, 1004), (490, 1005), (491, 1006), (492, 1007), (493, 1008), (494, 1009), (495, 1010), (496, 1011), (497, 1012), (498, 1013), (499, 1014), (500, 1015), (501, 1016), (502, 1017), (503, 1018), (504, 1019), (505, 1020), (506, 1021), (507, 1022), (508, 1023), (509, 1024), (510, 1025), (511, 1026), (512, 1027), (513, 1028), (514, 1029), (515, 1030), (516, 1031), (517, 1032), (518, 1033), (519, 1034), (520, 1035), (521, 1036), (522, 1037), (523, 1038), (524, 1039), (525, 1040), (526, 1041), (527, 1042)]
def layout : Aperture lowerPairs upperPairs 270 1708 1706 1707 ports255 (W.compactSkywalkTickLayout base 255) (OB5.sig 254) 144 where
  a:=[415, 416, 417, 418]
  b:=[930, 931, 932, 933]
  spec:=⟨by decide,by decide,[1703, 1704, 1705, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563],by decide +kernel⟩
  g0:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  na:=by decide +kernel
  nb:=by decide +kernel
  protected0:=by decide +kernel
  temps:=by decide +kernel

theorem from_full (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^129)
    (p:PackedCut lowerPairs upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u) (decide (Shadow.far 129 15 z))
        (decide (Shadow.far 129 15 z ∧ 2^129≤z.u)) (pullState (OB5.sig 254) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run Partial.enter255 m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof.forward,next.basis (map255 q)=(shadowRow 129 15 z G S).testBit q) ∧
      ∀q∉wires Partial.enter255,next.basis q=v.basis q := by
  have src:=read_packed layout raw v z G S p input
  apply actual_shadow map255 Partial.enter255 false 129 15 z G S small inc255 emitted255 v m
  intro q h
  have lim:wires EnterProof.forward ⊆ Finset.range 23 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have sz:ports255.length=23:=rfl
  have hv:=bitAt ports255 v.basis q (sz ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv
#print axioms from_full
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BarrelBits
open Partial Leave225Barrel Leave225Control Leave225Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
theorem byDigits (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^97) (h : holds wire 112 x s) (clean : s.basis 1613=false)
    (bit0 : parity s.basis controls0 = key.val.testBit 0)
    (bit1 : parity s.basis controls1 = key.val.testBit 1)
    (bit2 : parity s.basis controls2 = key.val.testBit 2)
    (bit3 : parity s.basis controls3 = key.val.testBit 3) :
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
    · rw [bit0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 112 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 97+(key.val % 2) ≤ 98)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 112 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 97+(key.val % 4) ≤ 100)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 112 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 97+(key.val % 8) ≤ 104)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave225BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Middle
open Arithmetic Partial Leave225Barrel Leave225High Leave225Word Leave225Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave225.drop 334).take 1744)
abbrev lastPart := ((leave225.drop 2080).take 108)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave225.drop 334).take 1854)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (key : Fin 16) (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (_one : ∀ q ∈ Leave225Join.tags, s.basis q = decide (q = Leave225Join.tags.getD key 0)),
    let x := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    Result wire 112 (x <<< key.val) s (run early m s))
    (wordLaw : ∀ (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (_tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (_shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (_digit : X/2^key.val = (s.basis 1724).toNat + 2*(s.basis 1613).toNat)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1724).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 112, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 112 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let H := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw key s m clean selectZero padding one
  have bits (i : Fin 112) : v.basis (wire i.val)=(2^key.val*H).testBit i.val := by
    rw [Nat.mul_comm (2^key.val) H,← Nat.shiftLeft_eq]
    exact a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 112, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 112, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 401+j.val≠1613 ∧ ∀ i : Fin 112, 401+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 112) : 1613 ≠ wire i.val := Leave225Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=hot key q := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (one q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (401+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=(2^key.val*H).testBit i := by
    let j : Fin 112 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have select : v.basis 1613=false := (a.frame _ Leave225Shift.layout3.separate).trans selectZero
  have neg : v.basis 1597=s.basis 1597 := a.frame _ (fun i h => (by decide +kernel : ∀ j : Fin 112, 1597≠wire j.val) ⟨i,h⟩)
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u,run,writeBit,Function.update,select,neg]
  have cross := old 1724 (by decide) (by decide +kernel)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis 1724).toNat + 2*(u.basis 1613).toNat := by rw [cross,d1]; exact digit
  have word := wordLaw key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 112, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1724).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 112, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 112 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave225High.result Leave225Word.combine key X s m clean selectZero padding one shadow digit scratch
end ECDSAAdd.Entrant.StairPacket.Leave225Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearWord
open Partial Leave225Join Leave225Barrel Leave225Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem combine (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=false)
    (scratch : s.basis 1614=false) :
    let out := run ((leave225.drop 2080).take 108) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref : BasisState := fun _ => false
  have none : run digitPass m s = s := by
    apply digits_quiet digitSites
    intro i _ hi
    apply off
    rw [List.getD_eq_getElem _ _ (show i < tags.length from hi)]
    exact List.getElem_mem _
  have sch : schedule ref 18 false 0 columns = true := by decide +kernel
  have members : ∀ r∈columns, ∀ q∈r.hot, q∈tags := by decide +kernel
  have geom : ∀ i : Fin 18, (row i).shadow=401+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have inputs : columnsRead columns s.basis X 0 18 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change s.basis (row ix).shadow = _ ∧ s.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.mod_eq_of_lt bound,Nat.zero_add,Nat.mul_zero,Nat.zero_testBit,ix]
    exact And.intro (shadow i hi) (tube i hi)
  have v := reassemble 1614 columns ref s m X 0 18 sites disjoint (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [Leave225Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero,none]
  exact ⟨v.1,fun i => by simpa only [Nat.mul_zero,Nat.zero_add,Nat.mod_eq_of_lt bound] using v.2.1 i.val i.isLt,v.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave225NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BarrelBits
open Partial Leave240Barrel Leave240Control Leave240Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
theorem byDigits (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^105) (h : holds wire 120 x s) (clean : s.basis 1613=false)
    (bit0 : parity s.basis controls0 = key.val.testBit 0)
    (bit1 : parity s.basis controls1 = key.val.testBit 1)
    (bit2 : parity s.basis controls2 = key.val.testBit 2)
    (bit3 : parity s.basis controls3 = key.val.testBit 3) :
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
    · rw [bit0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 120 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 105+(key.val % 2) ≤ 106)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 120 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 105+(key.val % 4) ≤ 108)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 120 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 105+(key.val % 8) ≤ 112)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave240BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Middle
open Arithmetic Partial Leave240Barrel Leave240High Leave240Word Leave240Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave240.drop 334).take 1880)
abbrev lastPart := ((leave240.drop 2216).take 107)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave240.drop 334).take 1989)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (key : Fin 16) (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (_one : ∀ q ∈ Leave240Join.tags, s.basis q = decide (q = Leave240Join.tags.getD key 0)),
    let x := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    Result wire 120 (x <<< key.val) s (run early m s))
    (wordLaw : ∀ (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (_tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (_shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (_digit : X/2^key.val = (s.basis 1716).toNat + 2*(s.basis 1613).toNat)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1716).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 120, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 120 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let H := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw key s m clean selectZero padding one
  have bits (i : Fin 120) : v.basis (wire i.val)=(2^key.val*H).testBit i.val := by
    rw [Nat.mul_comm (2^key.val) H,← Nat.shiftLeft_eq]
    exact a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 120, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 120, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 408+j.val≠1613 ∧ ∀ i : Fin 120, 408+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 120) : 1613 ≠ wire i.val := Leave240Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=hot key q := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (one q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (408+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=(2^key.val*H).testBit i := by
    let j : Fin 120 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have select : v.basis 1613=false := (a.frame _ Leave240Shift.layout3.separate).trans selectZero
  have neg : v.basis 1597=s.basis 1597 := a.frame _ (fun i h => (by decide +kernel : ∀ j : Fin 120, 1597≠wire j.val) ⟨i,h⟩)
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u,run,writeBit,Function.update,select,neg]
  have cross := old 1716 (by decide) (by decide +kernel)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis 1716).toNat + 2*(u.basis 1613).toNat := by rw [cross,d1]; exact digit
  have word := wordLaw key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 120, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1716).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 120, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 120 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave240High.result Leave240Word.combine key X s m clean selectZero padding one shadow digit scratch
end ECDSAAdd.Entrant.StairPacket.Leave240Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearWord
open Partial Leave240Join Leave240Barrel Leave240Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem combine (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=false)
    (scratch : s.basis 1614=false) :
    let out := run ((leave240.drop 2216).take 107) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref : BasisState := fun _ => false
  have none : run digitPass m s = s := by
    apply digits_quiet digitSites
    intro i _ hi
    apply off
    rw [List.getD_eq_getElem _ _ (show i < tags.length from hi)]
    exact List.getElem_mem _
  have sch : schedule ref 18 false 0 columns = true := by decide +kernel
  have members : ∀ r∈columns, ∀ q∈r.hot, q∈tags := by decide +kernel
  have geom : ∀ i : Fin 18, (row i).shadow=408+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have inputs : columnsRead columns s.basis X 0 18 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change s.basis (row ix).shadow = _ ∧ s.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.mod_eq_of_lt bound,Nat.zero_add,Nat.mul_zero,Nat.zero_testBit,ix]
    exact And.intro (shadow i hi) (tube i hi)
  have v := reassemble 1614 columns ref s m X 0 18 sites disjoint (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [Leave240Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero,none]
  exact ⟨v.1,fun i => by simpa only [Nat.mul_zero,Nat.zero_add,Nat.mod_eq_of_lt bound] using v.2.1 i.val i.isLt,v.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave240NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BarrelBits
open Partial Leave255Barrel Leave255Control Leave255Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
theorem byDigits (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^112) (h : holds wire 127 x s) (clean : s.basis 1613=false)
    (bit0 : parity s.basis controls0 = key.val.testBit 0)
    (bit1 : parity s.basis controls1 = key.val.testBit 1)
    (bit2 : parity s.basis controls2 = key.val.testBit 2)
    (bit3 : parity s.basis controls3 = key.val.testBit 3) :
    Result wire 127 (x <<< key.val) s (run ((leave255.drop 892).take 1441) m s) := by
  rw [emitted]
  have beginPass : ∀ m, Result wire 127 (x <<< 0) s (run passes0 m s) := HighBankBarrel.start h
  have p1 : ∀ m, Result wire 127 (x <<< (key.val % 2)) s (run passes1 m s) := by
    apply next layout3 (by decide) (by decide) away0.1 _ clean (room small (by omega : 112+0 ≤ 112)) _ beginPass
    · have dis : ∀ q ∈ controls0, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit0]
      exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, Result wire 127 (x <<< (key.val % 4)) s (run passes2 m s) := by
    apply next layout3 (by decide) (by decide) away1.1 _ clean (room small (by omega : 112+(key.val % 2) ≤ 113)) _ p1
    · have dis : ∀ q ∈ controls1, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit1]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, Result wire 127 (x <<< (key.val % 8)) s (run passes3 m s) := by
    apply next layout3 (by decide) (by decide) away2.1 _ clean (room small (by omega : 112+(key.val % 4) ≤ 115)) _ p2
    · have dis : ∀ q ∈ controls2, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit2]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, Result wire 127 (x <<< key.val) s (run passes4 m s) := by
    apply next layout3 (by decide) (by decide) away3.1 _ clean (room small (by omega : 112+(key.val % 8) ≤ 119)) _ p3
    · have dis : ∀ q ∈ controls3, q ∉ bank3 := by decide +kernel
      intro q hq i hi eq
      change q = bank3.getD i 0 at eq
      rw [List.getD_eq_getElem _ _ (show i < bank3.length from hi)] at eq
      exact dis q hq (eq ▸ List.getElem_mem _)
    · rw [bit3]
      exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  exact p4 m

end ECDSAAdd.Entrant.StairPacket.Leave255BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Middle
open Arithmetic Partial Leave255Barrel Leave255High Leave255Word Leave255Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave255.drop 334).take 1999)
abbrev lastPart := ((leave255.drop 2335).take 108)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave255.drop 334).take 2109)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (key : Fin 16) (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (_one : ∀ q ∈ Leave255Join.tags, s.basis q = decide (q = Leave255Join.tags.getD key 0)),
    let x := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    Result wire 127 (x <<< key.val) s (run early m s))
    (wordLaw : ∀ (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (_tagsOn : ∀ q ∈ tags, s.basis q = hot key q)
    (_shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=(2^key.val*H).testBit i)
    (_digit : X/2^key.val = (s.basis 1709).toNat + 2*(s.basis 1613).toNat)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1709).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 127, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 127 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let H := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw key s m clean selectZero padding one
  have bits (i : Fin 127) : v.basis (wire i.val)=(2^key.val*H).testBit i.val := by
    rw [Nat.mul_comm (2^key.val) H,← Nat.shiftLeft_eq]
    exact a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 127, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 127, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 416+j.val≠1613 ∧ ∀ i : Fin 127, 416+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 127) : 1613 ≠ wire i.val := Leave255Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=hot key q := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (one q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (416+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=(2^key.val*H).testBit i := by
    let j : Fin 127 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have select : v.basis 1613=false := (a.frame _ Leave255Shift.layout3.separate).trans selectZero
  have neg : v.basis 1597=s.basis 1597 := a.frame _ (fun i h => (by decide +kernel : ∀ j : Fin 127, 1597≠wire j.val) ⟨i,h⟩)
  have d1 : u.basis 1613 = !s.basis 1597 := by
    simp [u,run,writeBit,Function.update,select,neg]
  have cross := old 1709 (by decide) (by decide +kernel)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis 1709).toNat + 2*(u.basis 1613).toNat := by rw [cross,d1]; exact digit
  have word := wordLaw key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 127, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (one : ∀ q ∈ tags, s.basis q = hot key q)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (digit : X/2^key.val = (s.basis 1709).toNat + 2*(!s.basis 1597).toNat)
    (scratch : s.basis 1614=false) :
    let H := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=(2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 127, 18 ≤ i.val → out.basis (wire i.val)=(2^key.val*H).testBit i.val) ∧
      (∀ q, q≠1613 → outside wire 127 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave255High.result Leave255Word.combine key X s m clean selectZero padding one shadow digit scratch
end ECDSAAdd.Entrant.StairPacket.Leave255Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearWord
open Partial Leave255Join Leave255Barrel Leave255Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem combine (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (tube : ∀ i < 18, s.basis (wire i)=false)
    (scratch : s.basis 1614=false) :
    let out := run ((leave255.drop 2335).take 108) m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q := by
  let ref : BasisState := fun _ => false
  have none : run digitPass m s = s := by
    apply digits_quiet digitSites
    intro i _ hi
    apply off
    rw [List.getD_eq_getElem _ _ (show i < tags.length from hi)]
    exact List.getElem_mem _
  have sch : schedule ref 18 false 0 columns = true := by decide +kernel
  have members : ∀ r∈columns, ∀ q∈r.hot, q∈tags := by decide +kernel
  have geom : ∀ i : Fin 18, (row i).shadow=416+i.val ∧ (row i).tube=wire i.val := by decide +kernel
  have inputs : columnsRead columns s.basis X 0 18 0 := by
    intro i hi
    let ix : Fin 18 := ⟨i,hi⟩
    change s.basis (row ix).shadow = _ ∧ s.basis (row ix).tube = _
    rw [(geom ix).1,(geom ix).2]
    simp only [Nat.mod_eq_of_lt bound,Nat.zero_add,Nat.mul_zero,Nat.zero_testBit,ix]
    exact And.intro (shadow i hi) (tube i hi)
  have v := reassemble 1614 columns ref s m X 0 18 sites disjoint (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [Leave255Join.emitted,run_append,run_take,show measurementCount digitPass=0 from (digits_counts _ _ _ _ _ _).2,List.drop_zero,none]
  exact ⟨v.1,fun i => by simpa only [Nat.mul_zero,Nat.zero_add,Nat.mod_eq_of_lt bound] using v.2.1 i.val i.isLt,v.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave255NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
attribute [local irreducible] run routed onRails cell
set_option maxHeartbeats 2000000

/-- An archive edit follows the first native tick. Its local preservation of
the active rails and first record suffices for the complete fifteen-step trace. -/
theorem split_run (j:Fin 23) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m n:List Bool)
    (ready:onRails j 0 z s.basis) (v:State)
    (active:onRails j 1 (SkywalkTrace.next z) v.basis)
    (first:cell (shape j) 0 (mappedBasis j v.basis)=
      cell (shape j) 0 (mappedBasis j (run (routed j 0 1) m s).basis)) :
    let out:=run (routed j 1 14) n v
    onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
    readCells (shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z := by
  have post:=route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have back:=route_records j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have front:=(route_records j 0 1 (by decide) z odd s m ready).1
  have firstValue:=congrArg List.head? front
  simp only [readCells,SkywalkTrace.trace,List.head?_cons,Option.some.injEq] at firstValue
  exact ⟨post.2,congr (congrArg List.cons ((back.2 0 (by decide)).trans (first.trans firstValue))) back.1⟩

#print axioms split_run
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed

/-- Every future raw S position is clean; prior history may already be byte-encoded. -/
theorem stock_history (d:Bool) (x p i:Nat) (s:State) (stage:Rolling1588.Integer.Stage base d x p i s.basis)
    (j:Nat) (after:i≤j) (limit:j<512) : s.basis (base (1028+j))=false:=by
  obtain ⟨raw,hraw,hs⟩:=stage
  have f:=(W.compactSkywalkStage_fields_iff base _ i (by omega) base_pool_nodup raw.basis).mp hraw
  have mem:base (1028+j)∈(W.compactSkywalkTickLayout base j).wires:=by
    change (W.compactSkywalkTickLayout base j).history∈_
    simp [SkywalkIntegerLayout.wires]
  rw [hs]
  have dis:=Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i j after limit
  exact (run_preserves_outside _ [] raw _ (fun h=>Finset.disjoint_left.mp dis h (List.mem_toFinset.mpr mem))).trans
    (f.2.2.2.2.1 j after limit).2
#print axioms stock_history
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def idx : Fin 23 := ⟨10,by decide⟩
def lowA : List Wire := List.range' 241 159
def lowB : List Wire := List.range' 786 159
def safe (q:Wire) : Prop := (q<241 ∨ 400≤q) ∧ (q<786 ∨ 945≤q)
instance (q:Wire) : Decidable (safe q) := by unfold safe;infer_instance
theorem noLow : ∀q∈ports225++[1723,1721,1722]++sites upperPairs,safe q := by decide +kernel
theorem programCover : wires Partial.enter225 ⊆ ports225.toFinset := by decide +kernel
theorem protects (q:Wire) (h:q∈lowA++lowB) : q∉wires Partial.enter225 ∧ q≠1723 ∧ q≠1721 ∧ q≠1722 ∧ q∉sites upperPairs := by
  have check : ∀w∈lowA++lowB, ¬safe w := by decide +kernel
  have bad := check q h
  have gone : q∉ports225++[1723,1721,1722]++sites upperPairs := fun mem=>bad (noLow q mem)
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨fun m=>gone.1.1 (List.mem_toFinset.mp (programCover m)),gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩
def placement : WordPlacement (b:=144) (k:=15) layout Partial.enter225 where
  lowA:=lowA
  lowB:=lowB
  al:=by decide +kernel
  bl:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  aTop:=by decide +kernel
  bTop:=by decide +kernel
  protected0:=protects
  portsCount:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def idx : Fin 23 := ⟨11,by decide⟩
def lowA : List Wire := List.range' 256 151
def lowB : List Wire := List.range' 786 151
def safe (q:Wire) : Prop := (q<256 ∨ 407≤q) ∧ (q<786 ∨ 937≤q)
instance (q:Wire) : Decidable (safe q) := by unfold safe;infer_instance
theorem noLow : ∀q∈ports240++[1715,1713,1714]++sites upperPairs,safe q := by decide +kernel
theorem programCover : wires Partial.enter240 ⊆ ports240.toFinset := by decide +kernel
theorem protects (q:Wire) (h:q∈lowA++lowB) : q∉wires Partial.enter240 ∧ q≠1715 ∧ q≠1713 ∧ q≠1714 ∧ q∉sites upperPairs := by
  have check : ∀w∈lowA++lowB, ¬safe w := by decide +kernel
  have bad := check q h
  have gone : q∉ports240++[1715,1713,1714]++sites upperPairs := fun mem=>bad (noLow q mem)
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨fun m=>gone.1.1 (List.mem_toFinset.mp (programCover m)),gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩
def placement : WordPlacement (b:=136) (k:=15) layout Partial.enter240 where
  lowA:=lowA
  lowB:=lowB
  al:=by decide +kernel
  bl:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  aTop:=by decide +kernel
  bTop:=by decide +kernel
  protected0:=protects
  portsCount:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def idx : Fin 23 := ⟨12,by decide⟩
def lowA : List Wire := List.range' 271 144
def lowB : List Wire := List.range' 786 144
def safe (q:Wire) : Prop := (q<271 ∨ 415≤q) ∧ (q<786 ∨ 930≤q)
instance (q:Wire) : Decidable (safe q) := by unfold safe;infer_instance
theorem noLow : ∀q∈ports255++[1708,1706,1707]++sites upperPairs,safe q := by decide +kernel
theorem programCover : wires Partial.enter255 ⊆ ports255.toFinset := by decide +kernel
theorem protects (q:Wire) (h:q∈lowA++lowB) : q∉wires Partial.enter255 ∧ q≠1708 ∧ q≠1706 ∧ q≠1707 ∧ q∉sites upperPairs := by
  have check : ∀w∈lowA++lowB, ¬safe w := by decide +kernel
  have bad := check q h
  have gone : q∉ports255++[1708,1706,1707]++sites upperPairs := fun mem=>bad (noLow q mem)
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨fun m=>gone.1.1 (List.mem_toFinset.mp (programCover m)),gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩
def placement : WordPlacement (b:=129) (k:=15) layout Partial.enter255 where
  lowA:=lowA
  lowB:=lowB
  al:=by decide +kernel
  bl:=by decide +kernel
  xa:=by decide +kernel
  xb:=by decide +kernel
  aTop:=by decide +kernel
  bTop:=by decide +kernel
  protected0:=protects
  portsCount:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearHigh
open Arithmetic Partial Leave225Barrel Leave225High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (off : ∀ q ∈ Leave225Join.tags, s.basis q=false) :
    let x := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    Result wire 112 x s (run ((leave225.drop 334).take 1744) m s) := by
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
  have keys : ∀ q ∈ Leave225Join.tags, t.basis q=false :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (off _ h)
  have quiet (xs : List Wire) (sub : ∀ q ∈ xs, q ∈ Leave225Join.tags) : parity t.basis xs = false := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [parity,keys q (sub _ (by simp)),Bool.false_xor,ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  have action := Leave225BarrelBits.byDigits 0 x t (m.drop (measurementCount p)) small data cold
    (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel))
  have initial : x = adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨(by simpa only [Fin.val_zero,Nat.shiftLeft_zero] using action.bits),action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 97 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave225NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearHigh
open Arithmetic Partial Leave240Barrel Leave240High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (off : ∀ q ∈ Leave240Join.tags, s.basis q=false) :
    let x := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    Result wire 120 x s (run ((leave240.drop 334).take 1880) m s) := by
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
  have keys : ∀ q ∈ Leave240Join.tags, t.basis q=false :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (off _ h)
  have quiet (xs : List Wire) (sub : ∀ q ∈ xs, q ∈ Leave240Join.tags) : parity t.basis xs = false := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [parity,keys q (sub _ (by simp)),Bool.false_xor,ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  have action := Leave240BarrelBits.byDigits 0 x t (m.drop (measurementCount p)) small data cold
    (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel))
  have initial : x = adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨(by simpa only [Fin.val_zero,Nat.shiftLeft_zero] using action.bits),action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 105 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave240NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearHigh
open Arithmetic Partial Leave255Barrel Leave255High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

theorem result (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (off : ∀ q ∈ Leave255Join.tags, s.basis q=false) :
    let x := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    Result wire 127 x s (run ((leave255.drop 334).take 1999) m s) := by
  let p := adjust ys carries 1709 1597
  let t := run p m s
  let x := regValue ys t.basis
  have ht := HighBankAdjust.correct ys carries 1709 1597 (by decide +kernel) (by decide +kernel) (by decide) s m clean
  have coord : ∀ i : Fin 112, wire i = ys.getD i 0 := by decide +kernel
  have pad : ∀ i : Fin 127, 112 ≤ i.val → wire i ∉ ys := by decide +kernel
  have small : x < 2^112 := regValue_lt ys t.basis
  have data : holds wire 127 x t := by
    intro i hi
    by_cases lo : i < 112
    · rw [coord ⟨i,lo⟩]
      exact bit_read ys i t.basis lo
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (pad ⟨i,hi⟩ (show 112 ≤ i by omega))).trans (padding i (by omega) hi)
  have cold : t.basis 1613=false := (ht.2.1 _ (by decide +kernel)).trans selectZero
  have untouched : ∀ q ∈ Leave255Join.tags, q ∉ ys := by decide +kernel
  have keys : ∀ q ∈ Leave255Join.tags, t.basis q=false :=
    fun q h => (ht.2.1 _ (untouched _ h)).trans (off _ h)
  have quiet (xs : List Wire) (sub : ∀ q ∈ xs, q ∈ Leave255Join.tags) : parity t.basis xs = false := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [parity,keys q (sub _ (by simp)),Bool.false_xor,ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  have action := Leave255BarrelBits.byDigits 0 x t (m.drop (measurementCount p)) small data cold
    (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel)) (quiet _ (by decide +kernel))
  have initial : x = adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597) := ht.2.2
  dsimp only
  rw [combined,run_append,run_take,←initial]
  refine ⟨(by simpa only [Fin.val_zero,Nat.shiftLeft_zero] using action.bits),action.phase.trans ht.1,fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem member
  have inside := coord ⟨i,hi⟩
  rw [List.getD_eq_getElem _ _ hi] at inside
  exact h i (by change i < 112 at hi; omega) (he.symm.trans inside.symm)

end ECDSAAdd.Entrant.StairPacket.Leave255NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem shadow_odd (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) :
    (Shadow.reduced b 15 z).v%2=1 := by
  by_cases f:Shadow.far b 15 z
  · have h:IntegerHigh.Rel 15 z (Shadow.reduced b 15 z):=(Shadow.represented _ _ _ small f).1
    suffices ∀x y:SkywalkNat.State,IntegerHigh.Rel 15 x y → x.v%2=1 → y.v%2=1 from this _ _ h odd
    intro x y rel
    cases rel with
    | left => exact id
    | right B s D _ =>
      change (B+32768*D)%2=1 → B%2=1
      omega
  · simpa [Shadow.reduced,f] using odd

theorem true_records (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) (G S:Bool) :
    let T:=Shadow.reduced b 15 z
    SkywalkTrace.trace 15 (encode G S T.u T.v)=SkywalkTrace.trace 15 (encode G S z.u z.v) := by
  by_cases f:Shadow.far b 15 z
  · have h:=(Shadow.represented _ _ _ small f).1
    have o:=shadow_odd b z small odd
    exact (IntegerHigh.trace_eq h G S G S (by omega) odd (by omega) o).symm
  · simp [Shadow.reduced,f]

theorem interrupted_row (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) (G S cross:Bool)
    (cells:List (Bool×Bool))
    (records:let T:=Shadow.reduced b 15 z
      cells=SkywalkTrace.trace 15 (encode G S T.u T.v)) :
    let far:=decide (Shadow.far b 15 z)
    let u:=far && afterFlags (decide (z.v<z.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) far u (far && cross) q := by
  rw [records.trans (true_records b z small odd G S)]
  by_cases f:Shadow.far b 15 z
  · simpa only [f,decide_true,Bool.true_and] using
      far_suffix 5 (Shadow.represented _ _ _ small f).1 G S cross (by omega) odd
  · simpa only [f,decide_false,Bool.false_and] using near_suffix 5 z G S (by omega) odd

#print axioms true_records
#print axioms interrupted_row
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction

theorem read_cells (p:Shape) (start count index:Nat) (b:BasisState) (h:index<count) :
    read (readCells p start count b) index=cell p (start+index) b := by
  induction count generalizing start index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp [StairArchiveRaw.read,readCells]
    | succ index =>
      change read (readCells p (start+1) count b) index=_
      simpa only [Nat.add_assoc,Nat.add_comm 1 index] using ih (start+1) index (by omega)

def nativeRawPort (j:Fin 23) (q:Nat) :=
  let p:=ports (shape j) (5+q/2)
  windowNet j (if q%2=0 then p.a0 else p.history)

theorem native_raw_read (j:Fin 23) (s:State) (q:Nat) (h:q<20) :
    let cells:=readCells (shape j) 0 15 (mappedBasis j s.basis)
    s.basis (nativeRawPort j q)=letterBit (read (cells.drop 5) (q/2)) q := by
  have head : ∀xs:List (Bool×Bool), read (xs.drop 5) (q/2)=read xs (5+q/2):=by
    intro xs
    simp only [StairArchiveRaw.read,List.getElem?_drop]
  dsimp only
  rw [head,read_cells _ 0 15 _ _ (by omega),Nat.zero_add]
  unfold nativeRawPort letterBit cell mappedBasis
  split <;> rfl

namespace ArchiveBoundary240
def sourceIdx : Fin 23 := ⟨10,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveBoundary240

namespace ArchiveBoundary255
def sourceIdx : Fin 23 := ⟨11,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveBoundary255

namespace ArchiveBoundary270
def sourceIdx : Fin 23 := ⟨12,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
theorem observed (before now:State)
    (kept:∀q:Fin 20,now.basis (rawPorts ⟨q,by omega⟩)=before.basis (rawPorts ⟨q,by omega⟩))
    (far u c:Bool) (tags:now.basis (rawPorts 20)=far ∧ now.basis (rawPorts 21)=u ∧ now.basis (rawPorts 22)=c) :
    let cells:=readCells (shape sourceIdx) 0 15 (mappedBasis sourceIdx before.basis)
    ∀i:Fin 157,i.val<23 → now.basis (rawPorts i)=rawBit (read (cells.drop 5)) far u c i := by
  dsimp only
  intro i bound
  by_cases young:i.val<20
  · let col:Fin 20:=⟨i,young⟩
    refine (kept col).trans ?_
    rw [chronological col]
    exact (native_raw_read sourceIdx before i young).trans (by simp [rawBit,young])
  · have eq:i=20 ∨ i=21 ∨ i=22:=by omega
    rcases eq with rfl|rfl|rfl
    · exact tags.1
    · exact tags.2.1
    · exact tags.2.2
end ArchiveBoundary270

#print axioms ArchiveBoundary270.observed
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def carryPorts := ((IntegerPacket.ports (StairPacket.shape idx) 0).carry).map (windowNet idx)
def rest := carryPorts.drop 8
theorem sourceCover : ∀q∈rest, OB5.sig 224 q∈(W.compactSkywalkTickLayout base 225).carry := by decide +kernel
theorem clearCover : ∀q∈ports225++[1723,1721,1722]++sites upperPairs,q∉rest := by decide +kernel
theorem parts : carryPorts=(ports225.drop 15)++rest := by decide +kernel
theorem hist_sources : ∀r:Fin 15, OB5.sig 224 (windowNet idx (IntegerPacket.ports (StairPacket.shape idx) r).history)=base (1028+225+r) := by decide +kernel
theorem live : FramePorts placement idx where
  a:=by decide +kernel
  bSites:=by decide +kernel
  prev:=by decide +kernel
  carry:=by
    intro q hq
    let v:=windowNet idx q
    have h : v∈carryPorts:=List.mem_map.mpr ⟨q,hq,rfl⟩
    rw [parts,List.mem_append] at h
    rcases h with h|h
    · exact Or.inl h
    · have absent : v∉ports225++[1723,1721,1722]++sites upperPairs:=fun inc=>clearCover v inc h
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
      exact Or.inr ⟨fun m=>absent.1.1 (List.mem_toFinset.mp (programCover m)),sourceCover _ h,absent.1.2.1,absent.1.2.2.1,absent.1.2.2.2,absent.2⟩
  ext:=by decide +kernel
  hist:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def carryPorts := ((IntegerPacket.ports (StairPacket.shape idx) 0).carry).map (windowNet idx)
def rest := carryPorts.drop 8
theorem sourceCover : ∀q∈rest, OB5.sig 239 q∈(W.compactSkywalkTickLayout base 240).carry := by decide +kernel
theorem clearCover : ∀q∈ports240++[1715,1713,1714]++sites upperPairs,q∉rest := by decide +kernel
theorem parts : carryPorts=(ports240.drop 15)++rest := by decide +kernel
theorem hist_sources : ∀r:Fin 15, OB5.sig 239 (windowNet idx (IntegerPacket.ports (StairPacket.shape idx) r).history)=base (1028+240+r) := by decide +kernel
theorem live : FramePorts placement idx where
  a:=by decide +kernel
  bSites:=by decide +kernel
  prev:=by decide +kernel
  carry:=by
    intro q hq
    let v:=windowNet idx q
    have h : v∈carryPorts:=List.mem_map.mpr ⟨q,hq,rfl⟩
    rw [parts,List.mem_append] at h
    rcases h with h|h
    · exact Or.inl h
    · have absent : v∉ports240++[1715,1713,1714]++sites upperPairs:=fun inc=>clearCover v inc h
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
      exact Or.inr ⟨fun m=>absent.1.1 (List.mem_toFinset.mp (programCover m)),sourceCover _ h,absent.1.2.1,absent.1.2.2.1,absent.1.2.2.2,absent.2⟩
  ext:=by decide +kernel
  hist:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def carryPorts := ((IntegerPacket.ports (StairPacket.shape idx) 0).carry).map (windowNet idx)
def rest := carryPorts.drop 8
theorem sourceCover : ∀q∈rest, OB5.sig 254 q∈(W.compactSkywalkTickLayout base 255).carry := by decide +kernel
theorem clearCover : ∀q∈ports255++[1708,1706,1707]++sites upperPairs,q∉rest := by decide +kernel
theorem parts : carryPorts=(ports255.drop 15)++rest := by decide +kernel
theorem hist_sources : ∀r:Fin 15, let q:=OB5.sig 254 (windowNet idx (IntegerPacket.ports (StairPacket.shape idx) r).history)
    q=base (1028+255+r) ∨ q=1812 ∨ 1800≤q ∧ q≤1811 := by decide +kernel
theorem carry_range : (W.compactSkywalkTickLayout base 255).carry=List.range' 1556 256 := by decide +kernel
theorem live : FramePorts placement idx where
  a:=by decide +kernel
  bSites:=by decide +kernel
  prev:=by decide +kernel
  carry:=by
    intro q hq
    let v:=windowNet idx q
    have h : v∈carryPorts:=List.mem_map.mpr ⟨q,hq,rfl⟩
    rw [parts,List.mem_append] at h
    rcases h with h|h
    · exact Or.inl h
    · have absent : v∉ports255++[1708,1706,1707]++sites upperPairs:=fun inc=>clearCover v inc h
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at absent
      exact Or.inr ⟨fun m=>absent.1.1 (List.mem_toFinset.mp (programCover m)),sourceCover _ h,absent.1.2.1,absent.1.2.2.1,absent.1.2.2.2,absent.2⟩
  ext:=by decide +kernel
  hist:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearMiddle
open Arithmetic Partial Leave225Barrel Leave225High Leave225Word Leave225Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave225.drop 334).take 1744)
abbrev lastPart := ((leave225.drop 2080).take 108)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave225.drop 334).take 1854)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (_off : ∀ q ∈ Leave225Join.tags, s.basis q=false),
    let x := adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597)
    Result wire 112 x s (run early m s))
    (wordLaw : ∀ (X : Nat) (_bound : X<2^18) (s : State) (m : List Bool)
    (_off : ∀ q ∈ tags, s.basis q=false)
    (_shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=false)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1724=false)
    (scratch : s.basis 1614=false) :
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 112, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 112 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw s m clean selectZero padding off
  have bankZero : adjusted (regValue ys s.basis) 97 (s.basis 1724) (s.basis 1597) = 0 := by
    rw [bank,crossZero]
    cases s.basis 1597 <;> decide
  have bits (i : Fin 112) : v.basis (wire i.val)=false := by
    simpa only [bankZero,Nat.zero_testBit] using a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 112, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 112, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 401+j.val≠1613 ∧ ∀ i : Fin 112, 401+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 112) : 1613 ≠ wire i.val := Leave225Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=false := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (off q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (401+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=false := by
    let j : Fin 112 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have word := wordLaw X bound u tape readTags readShadow readTube zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 112, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 97 ≤ i → i < 112 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (401+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1724=false)
    (scratch : s.basis 1614=false) :
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 112, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 112 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave225NearHigh.result Leave225NearWord.combine X bound s m clean selectZero padding off shadow bank crossZero scratch
end ECDSAAdd.Entrant.StairPacket.Leave225NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearMiddle
open Arithmetic Partial Leave240Barrel Leave240High Leave240Word Leave240Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave240.drop 334).take 1880)
abbrev lastPart := ((leave240.drop 2216).take 107)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave240.drop 334).take 1989)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (_off : ∀ q ∈ Leave240Join.tags, s.basis q=false),
    let x := adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597)
    Result wire 120 x s (run early m s))
    (wordLaw : ∀ (X : Nat) (_bound : X<2^18) (s : State) (m : List Bool)
    (_off : ∀ q ∈ tags, s.basis q=false)
    (_shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=false)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1716=false)
    (scratch : s.basis 1614=false) :
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 120, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 120 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw s m clean selectZero padding off
  have bankZero : adjusted (regValue ys s.basis) 105 (s.basis 1716) (s.basis 1597) = 0 := by
    rw [bank,crossZero]
    cases s.basis 1597 <;> decide
  have bits (i : Fin 120) : v.basis (wire i.val)=false := by
    simpa only [bankZero,Nat.zero_testBit] using a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 120, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 120, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 408+j.val≠1613 ∧ ∀ i : Fin 120, 408+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 120) : 1613 ≠ wire i.val := Leave240Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=false := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (off q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (408+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=false := by
    let j : Fin 120 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have word := wordLaw X bound u tape readTags readShadow readTube zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 120, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 105 ≤ i → i < 120 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (408+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1716=false)
    (scratch : s.basis 1614=false) :
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 120, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 120 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave240NearHigh.result Leave240NearWord.combine X bound s m clean selectZero padding off shadow bank crossZero scratch
end ECDSAAdd.Entrant.StairPacket.Leave240NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearMiddle
open Arithmetic Partial Leave255Barrel Leave255High Leave255Word Leave255Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

abbrev first := ((leave255.drop 334).take 1999)
abbrev lastPart := ((leave255.drop 2335).take 108)
abbrev signBit : Program := [.X 1613,.CX 1597 1613]
abbrev middle := ((leave255.drop 334).take 2109)

theorem split : middle = first ++ (signBit ++ lastPart) := by rfl

/-- Keep the semantic composition independent of the concrete prefix and suffix programs. -/
private theorem abstractMiddle (early late combined : Program)
    (parts : combined = early ++ (signBit ++ late))
    (highLaw : ∀ (s : State) (m : List Bool)
    (_clean : ∀ q ∈ carries, s.basis q=false) (_selectZero : s.basis 1613=false)
    (_padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (_off : ∀ q ∈ Leave255Join.tags, s.basis q=false),
    let x := adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597)
    Result wire 127 x s (run early m s))
    (wordLaw : ∀ (X : Nat) (_bound : X<2^18) (s : State) (m : List Bool)
    (_off : ∀ q ∈ tags, s.basis q=false)
    (_shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (_tube : ∀ i < 18, s.basis (wire i)=false)
    (_scratch : s.basis 1614=false),
    let out := run late m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i.val ∧ out.basis (row i).free=false) ∧
      ∀ q, (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q)
    (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1709=false)
    (scratch : s.basis 1614=false) :
    let out := run combined m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 127, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 127 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) := by
  let v := run early m s
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := highLaw s m clean selectZero padding off
  have bankZero : adjusted (regValue ys s.basis) 112 (s.basis 1709) (s.basis 1597) = 0 := by
    rw [bank,crossZero]
    cases s.basis 1597 <;> decide
  have bits (i : Fin 127) : v.basis (wire i.val)=false := by
    simpa only [bankZero,Nat.zero_testBit] using a.bits i.val i.isLt
  have unchanged (q : Wire) (ne : q≠1613) : u.basis q = v.basis q := by simp [u,run,writeBit,Function.update,ne]
  have old (q : Wire) (ne : q≠1613) (ext : ∀ i : Fin 127, q≠wire i.val) : u.basis q=s.basis q :=
    (unchanged q ne).trans (a.frame q (fun i h => ext ⟨i,h⟩))
  have tagsOutside : ∀ q ∈ tags, q≠1613 ∧ ∀ i : Fin 127, q≠wire i.val := by decide +kernel
  have shadows : ∀ j : Fin 18, 416+j.val≠1613 ∧ ∀ i : Fin 127, 416+j.val≠wire i.val := by decide +kernel
  have stable (i : Fin 127) : 1613 ≠ wire i.val := Leave255Shift.layout3.separate i.val i.isLt
  have readTags (q : Wire) (hq : q∈tags) : u.basis q=false := (old q (tagsOutside q hq).1 (tagsOutside q hq).2).trans (off q hq)
  have readShadow (i : Nat) (hi : i<18) : u.basis (416+i)=X.testBit i := by
    let j : Fin 18 := ⟨i,hi⟩
    exact (old _ (shadows j).1 (shadows j).2).trans (shadow i hi)
  have readTube (i : Nat) (hi : i<18) : u.basis (wire i)=false := by
    let j : Fin 127 := ⟨i,by omega⟩
    exact (unchanged _ (stable j).symm).trans (bits j)
  have zero := (old 1614 (by decide) (by decide +kernel)).trans scratch
  have word := wordLaw X bound u tape readTags readShadow readTube zero
  dsimp only
  rw [parts,run_append,run_take,run_append,run_take,show measurementCount signBit=0 from rfl,List.drop_zero]
  refine ⟨word.1.trans a.phase,word.2.1,?_,?_⟩
  · intro i hi
    have outsideRows : ∀ i : Fin 127, 18 ≤ i.val → ∀ r ∈ columns, wire i.val≠r.shadow ∧ wire i.val≠r.tube := by decide +kernel
    exact (word.2.2 _ (outsideRows i hi)).trans ((unchanged _ (stable i).symm).trans (bits i))
  · intro q ne ext away
    exact (word.2.2 q away).trans ((unchanged q ne).trans (a.frame q ext))


theorem result (X : Nat) (bound : X<2^18) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries, s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀ i : Nat, 112 ≤ i → i < 127 → s.basis (wire i)=false)
    (off : ∀ q ∈ tags, s.basis q=false)
    (shadow : ∀ i < 18, s.basis (416+i)=X.testBit i)
    (bank : regValue ys s.basis=0) (crossZero : s.basis 1709=false)
    (scratch : s.basis 1614=false) :
    let out := run middle m s
    out.phase=s.phase ∧
      (∀ i : Fin 18, out.basis (row i).keep=X.testBit i ∧ out.basis (row i).free=false) ∧
      (∀ i : Fin 127, 18 ≤ i.val → out.basis (wire i.val)=false) ∧
      (∀ q, q≠1613 → outside wire 127 q → (∀ r ∈ columns, q≠r.shadow ∧ q≠r.tube) → out.basis q=s.basis q) :=
  abstractMiddle first lastPart middle split Leave255NearHigh.result Leave255NearWord.combine X bound s m clean selectZero padding off shadow bank crossZero scratch
end ECDSAAdd.Entrant.StairPacket.Leave255NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
theorem ready_from_cut (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^144)
    (p:PackedCut lowerPairs upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
        (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) (pullState (OB5.sig 224) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 225) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+225+r))=false)  :
    let t:=run Partial.enter225 m v
    let T:=Shadow.reduced 144 15 z
    t.phase=v.phase ∧ onRails idx 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  obtain ⟨ph,body,outer⟩:=from_full raw v z G S m small p input
  refine ⟨ph,complete live _ G S small raw v _ p input body outer ?_⟩
  intro r
  rw [hist_sources];exact hist r
  
  
  
theorem launch (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (Partial.portal225++Partial.enter225) m origin
    let T:=Shadow.reduced 144 15 z
    out.phase=raw.phase ∧ ∃G S:Bool,onRails idx 0 (SkywalkRails.encode G S T.u T.v) out.basis := by
  obtain ⟨G,S,input⟩:=PortalValues.real_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw stage
  have first:=Portal225Flag.physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m stage G S input
  have small:=true_small seed p 225 (by omega) hp (by decide)
  have farEq (z:SkywalkNat.State):Shadow.far 144 15 z ↔ 3*2^160≤z.u+z.v:=by
    unfold Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
  have same:Shadow.far 144 15 z=(3*2^160≤z.u+z.v):=propext (farEq _)
  change PackedCut lowerPairs upperPairs 240 1723 1721 1722 _ (decide (3*2^160≤z.u+z.v))
    (decide (3*2^160≤z.u+z.v ∧ 2^144≤z.u)) _ _ at first
  have normalized:PackedCut lowerPairs upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
      (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) (pullState (OB5.sig 224) raw) (run Partial.portal225 m (pullState (OB5.sig 224) raw)):=by
    simpa only [same] using first
  have h:=ready_from_cut raw _ z G S (m.drop (measurementCount Partial.portal225)) small normalized input
    (fun r=>by simpa only [Nat.add_assoc] using stock_history d seed p 225 raw stage (225+r) (by omega) (by have hr:=r.isLt;omega))
  simp only [run_append,run_take]
  exact ⟨h.1.trans first.phase, G,S,h.2⟩
#print axioms launch
#print axioms ready_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
theorem ready_from_cut (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^136)
    (p:PackedCut lowerPairs upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
        (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u)) (pullState (OB5.sig 239) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false)  :
    let t:=run Partial.enter240 m v
    let T:=Shadow.reduced 136 15 z
    t.phase=v.phase ∧ onRails idx 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  obtain ⟨ph,body,outer⟩:=from_full raw v z G S m small p input
  refine ⟨ph,complete live _ G S small raw v _ p input body outer ?_⟩
  intro r
  rw [hist_sources];exact hist r
  
  
  
#print axioms ready_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
theorem ready_from_cut (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool) (small:min z.u z.v<2^129)
    (p:PackedCut lowerPairs upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
        (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u)) (pullState (OB5.sig 254) raw) v)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false) :
    let t:=run Partial.enter255 m v
    let T:=Shadow.reduced 129 15 z
    t.phase=v.phase ∧ onRails idx 0 (SkywalkRails.encode G S T.u T.v) t.basis := by
  obtain ⟨ph,body,outer⟩:=from_full raw v z G S m small p input
  refine ⟨ph,complete live _ G S small raw v _ p input body outer ?_⟩
  intro r
  rcases hist_sources r with eq|eq|⟨lo,hi⟩
  · rw [eq];exact hist r
  · rw [eq];exact endScratch
  · apply (regValue_zero _ _).mp input.2.2.2.2.2;rw [carry_range,List.mem_range'_1];simp only [Wire] at *;omega
#print axioms ready_from_cut
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225OutputPorts
open Arithmetic Leave225Word Leave225Barrel LeaveCompanion225
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def live (i : Nat) : Wire := if h : i<18 then (row ⟨i,h⟩).keep else wire i
def scanned := 408::409::pendingPairs.map Prod.fst

theorem outputRegisters (s : State) (Z : Nat) (bits : ∀i<112, s.basis (live i)=Z.testBit i) :
    regValue smallA s.basis=Z%2^10 ∧ regValue scanned s.basis=(Z/2^7)%2^105 := by
  constructor
  · apply EnterProof.value_of_bits smallA
    intro i hi
    have h : ∀i:Fin 10,smallA.getD i 0=live i := by decide +kernel
    rw [h ⟨i,hi⟩]
    exact bits i (by change i<10 at hi;omega)
  · apply EnterProof.value_of_bits scanned
    intro i hi
    have h : ∀i:Fin 105,scanned.getD i 0=live (7+i.val) := by decide +kernel
    rw [h ⟨i,hi⟩,Nat.testBit_div_two_pow,Nat.add_comm i 7]
    apply bits
    change i<105 at hi
    omega

theorem activeBits (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=(2^k.val*H+X%2^k.val).testBit i.val)
    (hi : ∀i:Fin 112,18 ≤ i.val → s.basis (wire i.val)=(2^k.val*H).testBit i.val) :
    ∀i<112,s.basis (live i)=(2^k.val*H+X%2^k.val).testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h)]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i=false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a,Bool.false_xor] using z.2

theorem inactiveBits (X : Nat) (small : X<2^18) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=X.testBit i.val)
    (hi : ∀i:Fin 112,18 ≤ i.val → s.basis (wire i.val)=false) :
    ∀i<112,s.basis (live i)=X.testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h),Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

end ECDSAAdd.Entrant.StairPacket.Leave225OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240OutputPorts
open Arithmetic Leave240Word Leave240Barrel LeaveCompanion240
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def live (i : Nat) : Wire := if h : i<18 then (row ⟨i,h⟩).keep else wire i
def scanned := 416::417::pendingPairs.map Prod.fst

theorem outputRegisters (s : State) (Z : Nat) (bits : ∀i<120, s.basis (live i)=Z.testBit i) :
    regValue smallA s.basis=Z%2^11 ∧ regValue scanned s.basis=(Z/2^8)%2^112 := by
  constructor
  · apply EnterProof.value_of_bits smallA
    intro i hi
    have h : ∀i:Fin 11,smallA.getD i 0=live i := by decide +kernel
    rw [h ⟨i,hi⟩]
    exact bits i (by change i<11 at hi;omega)
  · apply EnterProof.value_of_bits scanned
    intro i hi
    have h : ∀i:Fin 112,scanned.getD i 0=live (8+i.val) := by decide +kernel
    rw [h ⟨i,hi⟩,Nat.testBit_div_two_pow,Nat.add_comm i 8]
    apply bits
    change i<112 at hi
    omega

theorem activeBits (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=(2^k.val*H+X%2^k.val).testBit i.val)
    (hi : ∀i:Fin 120,18 ≤ i.val → s.basis (wire i.val)=(2^k.val*H).testBit i.val) :
    ∀i<120,s.basis (live i)=(2^k.val*H+X%2^k.val).testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h)]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i=false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a,Bool.false_xor] using z.2

theorem inactiveBits (X : Nat) (small : X<2^18) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=X.testBit i.val)
    (hi : ∀i:Fin 120,18 ≤ i.val → s.basis (wire i.val)=false) :
    ∀i<120,s.basis (live i)=X.testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h),Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

end ECDSAAdd.Entrant.StairPacket.Leave240OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255OutputPorts
open Arithmetic Leave255Word Leave255Barrel LeaveCompanion255
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def live (i : Nat) : Wire := if h : i<18 then (row ⟨i,h⟩).keep else wire i
def scanned := 423::424::pendingPairs.map Prod.fst

theorem outputRegisters (s : State) (Z : Nat) (bits : ∀i<127, s.basis (live i)=Z.testBit i) :
    regValue smallA s.basis=Z%2^10 ∧ regValue scanned s.basis=(Z/2^7)%2^120 := by
  constructor
  · apply EnterProof.value_of_bits smallA
    intro i hi
    have h : ∀i:Fin 10,smallA.getD i 0=live i := by decide +kernel
    rw [h ⟨i,hi⟩]
    exact bits i (by change i<10 at hi;omega)
  · apply EnterProof.value_of_bits scanned
    intro i hi
    have h : ∀i:Fin 120,scanned.getD i 0=live (7+i.val) := by decide +kernel
    rw [h ⟨i,hi⟩,Nat.testBit_div_two_pow,Nat.add_comm i 7]
    apply bits
    change i<120 at hi
    omega

theorem activeBits (X H : Nat) (k : Fin 16) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=(2^k.val*H+X%2^k.val).testBit i.val)
    (hi : ∀i:Fin 127,18 ≤ i.val → s.basis (wire i.val)=(2^k.val*H).testBit i.val) :
    ∀i<127,s.basis (live i)=(2^k.val*H+X%2^k.val).testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h)]
    have z := HighBankJoin.merged_bits X H k.val i
    have kval := k.isLt
    have a : (X%2^k.val).testBit i=false := by simpa only [if_pos (show k.val ≤ i by omega)] using z.1
    simpa only [a,Bool.false_xor] using z.2

theorem inactiveBits (X : Nat) (small : X<2^18) (s : State)
    (lo : ∀i:Fin 18,s.basis (row i).keep=X.testBit i.val)
    (hi : ∀i:Fin 127,18 ≤ i.val → s.basis (wire i.val)=false) :
    ∀i<127,s.basis (live i)=X.testBit i := by
  intro i bound
  by_cases h : i<18
  · simpa only [live,dif_pos h] using lo ⟨i,h⟩
  · rw [live,dif_neg h,hi ⟨i,bound⟩ (by simpa using h),Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))]

end ECDSAAdd.Entrant.StairPacket.Leave255OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket
def watch (j:Fin 23) :=
  let p:=shape j
  let L:=ports p 1
  (L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem watch_congr (j:Fin 23) (s t:State) (agree:∀q∈watch j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:onRails j 1 z s.basis) :
    onRails j 1 z t.basis ∧ cell (shape j) 0 (mappedBasis j t.basis)=cell (shape j) 0 (mappedBasis j s.basis) := by
  let p:=shape j
  let L:=ports p 1
  let S:=mappedBasis j s.basis
  let T:=mappedBasis j t.basis
  have locality (q:Wire) (mem:q∈L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++[(ports p 0).a0,(ports p 0).history]) :
      T q=S q := agree _ (List.mem_map.mpr ⟨q,mem,rfl⟩)
  have add (xs:List Wire) (incl:∀q∈xs,T q=S q) : signedRegValue xs T=signedRegValue xs S:=by
    unfold signedRegValue;rw [regValue_congr _ _ _ incl]
  obtain ⟨a,b,prev,carry,free⟩:=active
  refine ⟨⟨(add _ (fun q h=>locality _ (by simp [L,p,h]))).trans a,
    (add _ (fun q h=>locality _ (by simp [L,p,h]))).trans b,
    (locality _ (by simp [L,p])).trans prev,
    (regValue_congr _ _ _ (fun q h=>locality _ (by simp [L,p,h]))).trans carry,?_⟩,?_⟩
  · intro r hr last
    have inRange:r∈List.range' 1 14:=by rw [List.mem_range'_1];exact ⟨hr,last⟩
    obtain ⟨e,h⟩:=free r hr last
    exact ⟨(locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans e,
      (locality _ (by simp only [List.mem_append];left;right;apply List.mem_flatMap.mpr;exact ⟨r,inRange,by simp [p]⟩)).trans h⟩
  · exact Prod.ext (locality _ (by simp [L,p])) (locality _ (by simp [L,p]))

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace NativePack225
def idx : Fin 23 := ⟨10,by decide⟩
def program (d:Bool) := renameProgram (OB5.sig 225) (Rolling1588.packAtTick d 225)
def reverse (d:Bool) := renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick d 225)
def support := ((List.range' 220 5).flatMap fun v=>[OB5.sig 225 (base v),OB5.sig 225 (base (1028+v))])
theorem packs (d:Bool) : wires (program d)⊆support.toFinset := by cases d <;> decide +kernel
theorem unpacks (d:Bool) : wires (reverse d)⊆support.toFinset := by cases d <;> decide +kernel
theorem disjoint : ∀q∈support,q∉watch idx := by decide +kernel
theorem retains (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈watch idx,(run (if back then reverse d else program d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈support.toFinset:=by cases back
                                   · exact packs d used
                                   · exact unpacks d used
  exact disjoint _ (List.mem_toFinset.mp seen) hq
end NativePack225
namespace NativePack240
def idx : Fin 23 := ⟨11,by decide⟩
def program (d:Bool) := renameProgram (OB5.sig 240) (Rolling1588.packAtTick d 230)
def reverse (d:Bool) := renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick d 230)
def support := ((List.range' 225 5).flatMap fun v=>[OB5.sig 240 (base v),OB5.sig 240 (base (1028+v))])
theorem packs (d:Bool) : wires (program d)⊆support.toFinset := by cases d <;> decide +kernel
theorem unpacks (d:Bool) : wires (reverse d)⊆support.toFinset := by cases d <;> decide +kernel
theorem disjoint : ∀q∈support,q∉watch idx := by decide +kernel
theorem retains (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈watch idx,(run (if back then reverse d else program d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈support.toFinset:=by cases back
                                   · exact packs d used
                                   · exact unpacks d used
  exact disjoint _ (List.mem_toFinset.mp seen) hq
end NativePack240
namespace NativePack255
def idx : Fin 23 := ⟨12,by decide⟩
def program (d:Bool) := renameProgram (OB5.sig 255) (Rolling1588.packAtTick d 245)
def reverse (d:Bool) := renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick d 245)
def support := ((List.range' 240 5).flatMap fun v=>[OB5.sig 255 (base v),OB5.sig 255 (base (1028+v))])
theorem packs (d:Bool) : wires (program d)⊆support.toFinset := by cases d <;> decide +kernel
theorem unpacks (d:Bool) : wires (reverse d)⊆support.toFinset := by cases d <;> decide +kernel
theorem disjoint : ∀q∈support,q∉watch idx := by decide +kernel
theorem retains (d back:Bool) (s:State) (m:List Bool) :
    ∀q∈watch idx,(run (if back then reverse d else program d) m s).basis q=s.basis q:=by
  intro q hq
  apply run_preserves_outside
  intro used
  have seen:q∈support.toFinset:=by cases back
                                   · exact packs d used
                                   · exact unpacks d used
  exact disjoint _ (List.mem_toFinset.mp seen) hq
end NativePack255
#print axioms NativePack255.retains
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

theorem archive_blank (d:Bool) (i:Fin 157) (h:16≤ i.val) : get (code d) i=0 := by
  by_cases low:i.val<23
  · have table:∀j:Fin 23,16≤ j.val → get (code d) j=0 := by cases d <;> decide +kernel
    exact table ⟨i,low⟩ h
  · exact (blank true d i (by omega)).2

namespace ArchiveBoundary240
def nextIdx : Fin 23 := ⟨11,by decide⟩
theorem scratch_carry : ∀i:Fin 157,23≤ i.val → rawPorts i∈((ports (shape nextIdx) 1).carry.map (windowNet nextIdx)) := by decide +kernel
theorem scratch_code : ∀i:Fin 157,23≤ i.val → rawPorts i=codePorts ⟨i.val-7,by omega⟩ := by decide +kernel
theorem past_only : ∀i:Fin 23,rawPorts ⟨i,by omega⟩∉watch nextIdx := by decide +kernel
theorem retain_watch (d:Bool) (z:SkywalkRails.State) (row:Nat) (s t:State)
    (on:onRails nextIdx 1 z s.basis) (frame:Frame codePorts (code d) row t)
    (outside:∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) :
    ∀q∈watch nextIdx,t.basis q=s.basis q := by
  intro q h
  by_cases mem:∃i,rawPorts i=q
  · obtain ⟨i,rfl⟩:=mem
    have hi:23≤ i.val:=by
      by_contra! bad
      exact past_only ⟨i,bad⟩ h
    obtain ⟨c,hc,eq⟩:=List.mem_map.mp (scratch_carry i hi)
    have fresh:rawPorts i=windowNet nextIdx c:=eq.symm
    have old:s.basis (rawPorts i)=false:=fresh ▸ (regValue_zero _ _).mp on.2.2.2.1 _ hc
    rw [old,scratch_code i hi,frame,archive_blank _ _ (by dsimp;omega),Nat.zero_testBit]
  · exact outside _ (fun i eq=>mem ⟨i,eq⟩)
end ArchiveBoundary240

namespace ArchiveBoundary255
def nextIdx : Fin 23 := ⟨12,by decide⟩
theorem scratch_carry : ∀i:Fin 157,23≤ i.val → rawPorts i∈((ports (shape nextIdx) 1).carry.map (windowNet nextIdx)) := by decide +kernel
theorem scratch_code : ∀i:Fin 157,23≤ i.val → rawPorts i=codePorts ⟨i.val-7,by omega⟩ := by decide +kernel
theorem past_only : ∀i:Fin 23,rawPorts ⟨i,by omega⟩∉watch nextIdx := by decide +kernel
theorem retain_watch (d:Bool) (z:SkywalkRails.State) (row:Nat) (s t:State)
    (on:onRails nextIdx 1 z s.basis) (frame:Frame codePorts (code d) row t)
    (outside:∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q) :
    ∀q∈watch nextIdx,t.basis q=s.basis q := by
  intro q h
  by_cases mem:∃i,rawPorts i=q
  · obtain ⟨i,rfl⟩:=mem
    have hi:23≤ i.val:=by
      by_contra! bad
      exact past_only ⟨i,bad⟩ h
    obtain ⟨c,hc,eq⟩:=List.mem_map.mp (scratch_carry i hi)
    have fresh:rawPorts i=windowNet nextIdx c:=eq.symm
    have old:s.basis (rawPorts i)=false:=fresh ▸ (regValue_zero _ _).mp on.2.2.2.1 _ hc
    rw [old,scratch_code i hi,frame,archive_blank _ _ (by dsimp;omega),Nat.zero_testBit]
  · exact outside _ (fun i eq=>mem ⟨i,eq⟩)
end ArchiveBoundary255

#print axioms ArchiveBoundary255.retain_watch
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem return_packed {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k))
    (map:Wire→Wire) (p r:Program) (inj:∀a c:Fin width,map a=map c→a=c)
    (map_eq:∀q:Wire,map q=rs.getD q 0) (sz:rs.length=width)
    (pf:p=renameProgram map forward) (pr:r=renameProgram map backward)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (small:min z.u z.v<2^b)
    (h:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (m t:List Bool) : run r t (run p m cut)=cut := by
  have sup : wires forward=wires backward := by decide +kernel
  have lim:wires forward ⊆ Finset.range width := by apply ArchiveFieldScratch.bounded;decide +kernel
  have src:=read_packed A raw cut z G S h input
  have initial (q:Wire) (hq:q∈wires forward):cut.basis (map q)=(initialRow b k z G S).testBit q:=by
    rw [map_eq]
    have hv:=bitAt rs cut.basis q (sz ▸ Finset.mem_range.mp (lim hq))
    rwa [src] at hv
  have first:=actual_shadow map p false b k z G S small inj pf cut m initial
  have last:=actual_shadow map r true b k z G S small inj pr (run p m cut) t
    (fun q hq=>first.2.1 q (sup ▸ hq))
  apply congrArg₂ State.mk (last.1.trans first.1)
  funext q
  have pp:wires p=(wires forward).image map:=pf ▸ JointForward1588.wires_rename_image _ _
  have rr:wires r=wires p:=by rw [pr,JointForward1588.wires_rename_image,←sup,pp]
  by_cases mem:q∈wires p
  · obtain ⟨v,vh,rfl⟩:=Finset.mem_image.mp (pp ▸ mem)
    exact (last.2.1 _ (sup ▸ vh)).trans (initial _ vh).symm
  · exact (last.2.2 q (rr ▸ mem)).trans (first.2.2 _ mem)
#print axioms return_packed
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run routed unrouted onRails cell

def body (j:Fin 23) (admin:Program) := routed j 0 1 ++ (admin ++ routed j 1 14)
def unbody (j:Fin 23) (reverse:Program) := unrouted j 1 14 ++ (reverse ++ unrouted j 0 1)

structure AdminResult (j:Fin 23) (reverse:Program) (src out:State) : Prop where
  phase : out.phase=src.phase
  unchanged : ∀q∈watch j,out.basis q=src.basis q
  undo : ∀m,run reverse m out=src

theorem body_run (j:Fin 23) (admin reverse:Program) (s:State) (m:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:onRails j 0 z s.basis)
    (mid:let src:=run (routed j 0 1) m s
      AdminResult j reverse src (run admin (m.drop (measurementCount (routed j 0 1))) src)) :
    let out:=run (body j admin) m s
    out.phase=s.phase ∧ onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbody j reverse) n out=s := by
  let src:=run (routed j 0 1) m s
  let t:=m.drop (measurementCount (routed j 0 1))
  let pre:=run admin t src
  let n:=t.drop (measurementCount admin)
  have head:=route_frame j 0 1 (by decide) z odd s m active
  have valid:onRails j 1 (SkywalkTrace.next z) src.basis:=head.2
  have pass:=watch_congr j src pre mid.unchanged _ valid
  have span:=split_run j z odd s m n active pre pass.1 pass.2
  have last:=route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n pass.1
  dsimp only [body,unbody]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack:=route_undo j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n r pass.1
  change run (unrouted j 0 1) _ (run reverse _ (run (unrouted j 1 14) r (run (routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact route_undo j 0 1 (by decide) z odd s m _ active

namespace NativePack225
def history (q:Fin 10) := OB5.sig 225 (History5.historyMap base 220 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack225

namespace NativePack240
def history (q:Fin 10) := OB5.sig 240 (History5.historyMap base 225 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack240

namespace NativePack255
def history (q:Fin 10) := OB5.sig 255 (History5.historyMap base 240 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack255

namespace NativePack270
def program (d:Bool) := renameProgram (OB5.sig 270) (Rolling1588.packAtTick d 260)
def reverse (d:Bool) := renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick d 260)
end NativePack270
namespace NativePack270
def history (q:Fin 10) := OB5.sig 270 (History5.historyMap base 255 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack270

#print axioms body_run
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run routed unrouted onRails cell
namespace NativePack225
theorem admin (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    AdminResult idx (reverse d) s (run (program d) m s) :=
  ⟨(source_law d s m ok).1,retains d false s m,(source_law d s m ok).2⟩
end NativePack225

namespace NativePack240
open ArchiveBoundary240
def withArchive (d:Bool) := program d ++ Partial.archiveLoad240 d
def fromArchive (d:Bool) := Partial.archiveRestore240 d ++ reverse d

theorem admin (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (active:onRails idx 1 z s.basis) (ok:MeasuredCodec5.legalAt history s.basis)
    (row:Nat) (limit:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    let out:=run (withArchive d) m s
    AdminResult idx (fromArchive d) s out ∧ Frame codePorts (code d) row out := by
  let p:=run (program d) m s
  let tape:=m.drop (measurementCount (program d))
  let a:=run (Partial.archiveLoad240 d) tape p
  have old:=source_law d s m ok
  have stay:=retains d false s m
  have now:=watch_congr idx s p stay z active
  have arr:=load_run d row limit p tape raw
  have untouched:=retain_watch d z row p a now.1 arr.2.1 arr.2.2
  dsimp only [withArchive,fromArchive]
  simp only [run_append,run_take]
  refine ⟨⟨arr.1.trans old.1,fun q h=>(untouched _ h).trans (stay _ h),?_⟩,arr.2.1⟩
  intro n
  rw [run_append,run_take]
  change run (reverse d) _ (run (Partial.archiveRestore240 d) _ a)=s
  rw [roundtrip d row limit p tape _ raw]
  exact old.2 _
end NativePack240

namespace NativePack255
open ArchiveBoundary255
def withArchive (d:Bool) := program d ++ Partial.archiveLoad255 d
def fromArchive (d:Bool) := Partial.archiveRestore255 d ++ reverse d

theorem admin (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (active:onRails idx 1 z s.basis) (ok:MeasuredCodec5.legalAt history s.basis)
    (row:Nat) (limit:row<63145)
    (raw:Frame rawPorts ArchivePortAction.raw row (run (program d) m s)) :
    let out:=run (withArchive d) m s
    AdminResult idx (fromArchive d) s out ∧ Frame codePorts (code d) row out := by
  let p:=run (program d) m s
  let tape:=m.drop (measurementCount (program d))
  let a:=run (Partial.archiveLoad255 d) tape p
  have old:=source_law d s m ok
  have stay:=retains d false s m
  have now:=watch_congr idx s p stay z active
  have arr:=load_run d row limit p tape raw
  have untouched:=retain_watch d z row p a now.1 arr.2.1 arr.2.2
  dsimp only [withArchive,fromArchive]
  simp only [run_append,run_take]
  refine ⟨⟨arr.1.trans old.1,fun q h=>(untouched _ h).trans (stay _ h),?_⟩,arr.2.1⟩
  intro n
  rw [run_append,run_take]
  change run (reverse d) _ (run (Partial.archiveRestore255 d) _ a)=s
  rw [roundtrip d row limit p tape _ raw]
  exact old.2 _
end NativePack255

#print axioms NativePack255.admin
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run routed unrouted onRails cell
namespace NativePack225
def window (d:Bool) := body idx (program d)
def unwind (d:Bool) := unbody idx (reverse d)
theorem window_run (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (start:onRails idx 0 z s.basis)
    (legal:MeasuredCodec5.legalAt history (run (routed idx 0 1) m s).basis)
    : let out:=run (window d) m s
      out.phase=s.phase ∧ onRails idx 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind d) n out=s := by
  apply body_run _ _ _ _ _ z odd start
  exact admin d _ _ legal
end NativePack225
namespace NativePack240
def window (d:Bool) := body idx (withArchive d)
def unwind (d:Bool) := unbody idx (fromArchive d)
theorem window_run (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (start:onRails idx 0 z s.basis)
    (legal:MeasuredCodec5.legalAt history (run (routed idx 0 1) m s).basis)
    (row:Nat) (limit:row<63145) (frame:Frame ArchiveBoundary240.rawPorts raw row
      (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s)))
    : let out:=run (window d) m s
      out.phase=s.phase ∧ onRails idx 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind d) n out=s := by
  apply body_run _ _ _ _ _ z odd start
  exact (admin d _ _ (SkywalkTrace.next z) (route_frame idx 0 1 (by decide) z odd s m start).2 legal row limit frame).1
end NativePack240
namespace NativePack255
def window (d:Bool) := body idx (withArchive d)
def unwind (d:Bool) := unbody idx (fromArchive d)
theorem window_run (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (start:onRails idx 0 z s.basis)
    (legal:MeasuredCodec5.legalAt history (run (routed idx 0 1) m s).basis)
    (row:Nat) (limit:row<63145) (frame:Frame ArchiveBoundary255.rawPorts raw row
      (run (program d) (m.drop (measurementCount (routed idx 0 1))) (run (routed idx 0 1) m s)))
    : let out:=run (window d) m s
      out.phase=s.phase ∧ onRails idx 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind d) n out=s := by
  apply body_run _ _ _ _ _ z odd start
  exact (admin d _ _ (SkywalkTrace.next z) (route_frame idx 0 1 (by decide) z odd s m start).2 legal row limit frame).1
end NativePack255
#print axioms NativePack255.window_run
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run routed SkywalkIntegerLayout.wires

def firstUnchanged (j:Fin 23) (q:Wire) : Prop :=
  let r:=windowNet j q
  r=(ports (shape j) 0).previous ∨ r∉(ports (shape j) 0).wires
instance (j:Fin 23) (q:Wire) : Decidable (firstUnchanged j q) := by unfold firstUnchanged;infer_instance

theorem first_preserves (j:Fin 23) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m:List Bool)
    (ready:onRails j 0 z s.basis) (q:Wire) (free:firstUnchanged j q) :
    (run (routed j 0 1) m s).basis q=s.basis q := by
  let p:=shape j
  let L:=ports p 0
  let virt:=pullState (windowNet j) s
  let v:=windowNet j q
  have inv:windowNet j v=q:=by
    apply OB5.sig_invol
    have b:=j.isLt
    simp [start];omega
  have step:=pull_routed j 0 1 (by decide) m s
  simp only [seq,List.append_nil] at step
  have at_q:=congrArg (fun x:State=>x.basis v) step
  change (run (routed j 0 1) m s).basis (windowNet j v)=(run (skywalkIntegerTick L) m virt).basis v at at_q
  rw [inv] at at_q
  refine at_q.trans (Eq.trans ?_ (show virt.basis v=s.basis q from congrArg s.basis inv))
  rcases free with e|e
  · change v=L.previous at e
    rw [e]
    obtain ⟨ha,hb,hg,hc,hnew⟩:=ready
    obtain ⟨he,hh⟩:=hnew 0 (by decide) (by change 0<15;decide)
    obtain ⟨_,_,_,_,_,prev,_⟩:=executed p ⟨0,by change 0<15;decide⟩ _ _ _ odd virt m ⟨ha,hb,hg,he,hh,hc⟩
    exact prev.trans hg.symm
  · apply run_preserves_outside
    exact fun used=>e (List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok p ⟨0,by change 0<15;decide⟩)).1 used))

#print axioms first_preserves
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem preserve_readonly (P:Program) (q:Wire) (unused:∀i∈P,CodecBitSliceVerify.target i≠q)
    (s:State) (m:List Bool) : (run P m s).basis q=s.basis q := by
  induction P generalizing s m with
  | nil=>rfl
  | cons i rest ih=>
    change (run ([i]++rest) m s).basis q=s.basis q
    rw [run_append,ih (fun j h=>unused _ (List.mem_cons_of_mem _ h))]
    have neq:=unused i (by simp)
    cases i <;> simp only [CodecBitSliceVerify.target] at neq <;> simp [run,measureAndCorrect,writeBit,Ne.symm neq]

theorem legal_congr {a b:Fin 10→Wire} {s t:BasisState}
    (same:∀i,s (a i)=t (b i)) (ok:MeasuredCodec5.legalAt b t) : MeasuredCodec5.legalAt a s := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  simp only [same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp ok i

namespace NativePack225
theorem original_legal (d:Bool) (seed p:Nat) (hp0:0<p) (odd:p%2=1) (raw:State)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    MeasuredCodec5.legalAt (History5.historyMap base 220) raw.basis := by
  obtain ⟨pre,original,packed⟩:=stage
  rw [packed]
  apply Rolling1588.Integer.prefix_next_legal base d base_pool_nodup 225 (by decide) (by decide)
  exact W.stage_group_legal base base_pool_nodup seed p 225 220 hp0 odd (by decide) (by decide) _ original

theorem history_from_stock (raw cut t:State) {neg far long:Bool}
    (frame:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long
      (pullState (OB5.sig 224) raw) cut)
    (m n:List Bool) (head:t=run Partial.enter225 m cut)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (ready:onRails idx 0 z t.basis) :
    ∀i,(run (routed idx 0 1) n t).basis (history i)=raw.basis (History5.historyMap base 220 i) := by
  have first:∀i,firstUnchanged idx (history i):=by decide +kernel
  have enter:∀i,∀gate∈Partial.enter225,CodecBitSliceVerify.target gate≠history i:=by decide +kernel
  have cutSafe:∀i,history i≠1723 ∧ history i≠1721 ∧ history i≠1722 ∧ history i∉sites Enter225.upperPairs:=by decide +kernel
  have coord:∀i,OB5.sig 224 (history i)=History5.historyMap base 220 i:=by decide +kernel
  intro i
  rw [first_preserves idx z odd _ _ ready _ (first i),head,preserve_readonly _ _ (enter i)]
  obtain ⟨hn,hf,hu,hh⟩:=cutSafe i
  exact (frame.unchanged _ hn hf hu hh).trans (congrArg raw.basis (coord i))

#print axioms history_from_stock
end NativePack225
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run onRails routed unrouted

def firstWindow (d:Bool) := Partial.portal225 ++ (Partial.enter225 ++ window d)
def firstUnwind (d:Bool) := unwind d ++ (Partial.enter225Inv ++ Partial.portal225Inv)

theorem first_window (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d seed p 225 raw.basis) :
    let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 224) raw
    let out:=run (firstWindow d) m origin
    out.phase=raw.phase ∧ (∃G S:Bool,
      let T:=Shadow.reduced 144 15 z
      onRails idx 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (shape idx) 0 15 (mappedBasis idx out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v)) ∧
      ∀n,run (firstUnwind d) n out=origin := by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init seed p)
  let origin:=pullState (OB5.sig 224) raw
  let cut:=run Partial.portal225 m origin
  let n:=m.drop (measurementCount Partial.portal225)
  let pre:=run Partial.enter225 n cut
  let tape:=n.drop (measurementCount Partial.enter225)
  let T:=Shadow.reduced 144 15 z
  have small:min z.u z.v<2^144:=true_small seed p 225 (by omega) hp (by decide)
  obtain ⟨G,S,input⟩:=PortalValues.real_input d seed p 225 hp0 hx0 hpo hp hq hx hc (by decide) raw stage
  have pcut:=Portal225Flag.physical_frame_for d seed p hp0 hx0 hpo hp hq hx hc raw m stage G S input
  have same:Shadow.far 144 15 z=(3*2^160≤z.u+z.v):=by
    apply propext
    unfold Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have normalized:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
      (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) origin cut:=by
    simpa only [same] using pcut
  have ready:=Enter225.ready_from_cut raw cut z G S n small normalized input
    (fun r=>by simpa only [Nat.add_assoc] using stock_history d seed p 225 raw stage (225+r) (by omega) (by have hr:=r.isLt;omega))
  have zo:z.v%2=1:=(SkywalkNat.iter_valid 225 (SkywalkNat.init seed p) hp0 hpo).2.1
  have to':T.v%2=1:=shadow_odd 144 z small zo
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have initial:=original_legal d seed p hp0 hpo raw stage
  have legal:=legal_congr (history_from_stock raw cut pre pcut n tape rfl _ parity ready.2) initial
  have whole:=window_run d pre tape _ parity ready.2 legal
  dsimp only [firstWindow,firstUnwind]
  simp only [run_append,run_take]
  refine ⟨whole.1.trans (ready.1.trans pcut.phase),⟨G,S,whole.2.1,whole.2.2.1.trans (true_records 144 z small zo G S)⟩,?_⟩
  intro inv
  rw [whole.2.2.2 inv]
  have rollback:=return_packed Enter225.layout map225 _ _ inc225 (fun _=>rfl) rfl emitted225 emitted225Inv
    raw cut z G S small normalized input n
  rw [rollback]
  exact Portal225Flag.portal_return _ m _ (Portal225Flag.clean_for raw z G S input)
#print axioms first_window
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

