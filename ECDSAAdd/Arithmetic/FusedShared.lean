import ECDSAAdd.Arithmetic.FusedSharedIds
import ECDSAAdd.Arithmetic.FusedSignedHalfPacked

namespace ECDSAAdd.Arithmetic

/-- Packed forward kernel overlay. Guards and temporaries are borrowed from
the already cleared terminal rails and restored seed/integer workspace. -/
def fusedSharedPorts (w : Nat → Wire) (g : Wire) : FusedHalfPorts :=
  { b:=g,cin:=w 1797,low:=w 2056,e:=w 770,
    a:=w 512,h:=w 513,j:=w 514,l:=w 515,m:=w 516,
    qOut:=w 2312,hOut:=w 769,t:=w 1796,d:=w 2055,
    yg0:=w 1026,yg1:=w 1027,rTail:=wireBlock w 2057 255,
    yTail:=wireBlock w 771 255,C:=wireBlock w 1540 256,
    A:=wireBlock w 512 256,carry:=wireBlock w 1798 257++[w 2313] }

attribute [local irreducible] wireBlock

theorem fusedSharedPorts_widths (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).Widths := by
  constructor <;> simp [fusedSharedPorts,wireBlock_length]

private theorem fusedShared_block_one (w : Nat → Wire) (s : Nat) :
    wireBlock w s 1=[w s] := by simp [wireBlock,List.range']

theorem fusedSharedPorts_targetLow (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).targetLow=wireBlock w 2056 256 := by
  change w 2056::wireBlock w 2057 255=_
  simpa only [fusedShared_block_one,Nat.reduceAdd,List.singleton_append] using
    wireBlock_append w 2056 1 255

theorem fusedSharedPorts_source (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).source=wireBlock w 770 258 := by
  have hlow : w 770::wireBlock w 771 255=wireBlock w 770 256 := by
    simpa only [fusedShared_block_one,Nat.reduceAdd,List.singleton_append] using
      wireBlock_append w 770 1 255
  change (w 770::wireBlock w 771 255)++[w 1026,w 1027]=_
  rw [hlow]
  have htop : [w 1026,w 1027]=wireBlock w 1026 2 := by
    simpa only [fusedShared_block_one,Nat.reduceAdd,List.singleton_append] using
      wireBlock_append w 1026 1 1
  rw [htop,wireBlock_append]

theorem fusedSharedPorts_wires (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).wires=g::fusedSharedIds.map w := by
  have ht : (fusedSharedPorts w g).target=
      wireBlock w 2056 257++[w 769] := by
    change (fusedSharedPorts w g).targetLow++[w 2312,w 769]=_
    rw [fusedSharedPorts_targetLow]
    have he := wireBlock_append w 2056 256 1
    simp only [fusedShared_block_one,Nat.reduceAdd] at he
    rw [show [w 2312,w 769]=[w 2312]++[w 769] from rfl,
      ←List.append_assoc,he]
  have hc : (fusedSharedPorts w g).constant=
      wireBlock w 1540 257++[w 2055] := by
    change wireBlock w 1540 256++[w 1796,w 2055]=_
    have he := wireBlock_append w 1540 256 1
    simp only [fusedShared_block_one,Nat.reduceAdd] at he
    rw [show [w 1796,w 2055]=[w 1796]++[w 2055] from rfl,←List.append_assoc,he]
  change g::w 1797::((fusedSharedPorts w g).source++
    (fusedSharedPorts w g).target++(fusedSharedPorts w g).constant++
    (wireBlock w 1798 257++[w 2313])++wireBlock w 512 256)=_
  rw [fusedSharedPorts_source,ht,hc]
  simp only [fusedSharedIds,List.map_cons,List.map_append,List.map_nil,wireBlock]

theorem fusedSharedPorts_nodup (w : Nat → Wire) (g : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w) :
    (fusedSharedPorts w g).wires.Nodup := by
  rw [fusedSharedPorts_wires]
  exact fusedSharedSites_nodup w g hn hg

theorem fusedSharedPorts_early (w : Nat → Wire) (g : Wire) :
    (fusedSharedPorts w g).early.Sublist (fusedSharedPorts w g).A := by
  have he : (fusedSharedPorts w g).early=wireBlock w 512 5 := by
    change [w 512,w 513,w 514,w 515,w 516]=wireBlock w 512 5
    rw [wireBlock]
    rfl
  rw [he]
  change (wireBlock w 512 5).Sublist (wireBlock w 512 256)
  have ht := List.sublist_append_left (wireBlock w 512 5) (wireBlock w 517 251)
  have hb := wireBlock_append w 512 5 251
  norm_num only at hb
  rw [hb] at ht
  exact ht

/-- The record g means addition when true in the existing butterfly. The
packed arithmetic b means subtraction when true, so toggle/restore g. -/
def fusedSharedSignedHalf (w : Nat → Wire) (g : Wire) : Program :=
  [.X g]++(fusedSharedPorts w g).program++[.X g]

private theorem fused_toggle_counts (g : Wire) (P : Program) (t m : Nat)
    (hc : toffoliCount P=t ∧ measurementCount P=m) :
    toffoliCount ([.X g]++P++[.X g])=t ∧
    measurementCount ([.X g]++P++[.X g])=m := by
  have ht : toffoliCount [.X g]=0 := rfl
  have hm : measurementCount [.X g]=0 := rfl
  simp only [toffoliCount_append,measurementCount_append,ht,hm,hc.1,hc.2,
    Nat.zero_add,Nat.add_zero]
  trivial

/-- This is the same emitted stream, not a connected point-circuit saving. -/
theorem fusedSharedSignedHalf_counts (w : Nat → Wire) (g : Wire) :
    toffoliCount (fusedSharedSignedHalf w g)=1795 ∧
    measurementCount (fusedSharedSignedHalf w g)=1796 := by
  have hA : (fusedSharedPorts w g).A.length=256 := wireBlock_length w 512 256
  have hc := (fusedSharedPorts w g).counts (fusedSharedPorts_widths w g)
  have hn : toffoliCount (fusedSharedPorts w g).program=1795 ∧
      measurementCount (fusedSharedPorts w g).program=1796 := by
    simpa only [hA,Nat.reduceMul,Nat.reduceAdd] using hc
  unfold fusedSharedSignedHalf
  exact fused_toggle_counts g (fusedSharedPorts w g).program 1795 1796 hn

end ECDSAAdd.Arithmetic
