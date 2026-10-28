import ECDSAAdd.Arithmetic.OffsetBorrowedInverseParity
import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

def mapBit (f : Wire → Wire) (b : MappedBit) : MappedBit :=
  {wire:=b.wire.map f,flip:=b.flip}
def mapCleanup (f : Wire → Wire) (L : BalancedCleanup.Layout) : BalancedCleanup.Layout :=
  {r0:=f L.r0,rtail:=L.rtail.map f,rmsb:=f L.rmsb,
   ylow:=L.ylow.map f,ymsb:=f L.ymsb,carry:=L.carry.map f,
   sign:=f L.sign,parity:=f L.parity,lower:=f L.lower,one:=f L.one}
def mapCircuit (f : Wire → Wire) (L : BalancedCircuit.Layout) : BalancedCircuit.Layout :=
  {toLayout:=mapCleanup f L.toLayout,sourceGuard:=f L.sourceGuard,
   cout:=f L.cout,minus:=f L.minus,plus:=f L.plus}
def mapOffset (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) : BalancedCleanupOffset.Layout :=
  {toCircuit:=mapCircuit f L.toCircuit,offsetCarry:=L.offsetCarry.map f}

theorem low_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).low=L.low.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.low]
theorem r_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).r=L.r.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
theorem y_map (f : Wire → Wire) (L : BalancedCleanup.Layout) :
    (mapCleanup f L).y=L.y.map f := by
  simp [mapCleanup,BalancedCleanup.Layout.y]
theorem rawSource_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.rawSource (mapCircuit f L)=(BalancedCircuit.rawSource L).map f := by
  simp [BalancedCircuit.rawSource,mapCircuit,y_map]
theorem rawTarget_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.rawTarget (mapCircuit f L)=(BalancedCircuit.rawTarget L).map f := by
  simp [BalancedCircuit.rawTarget,mapCircuit,mapCleanup,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
theorem foldTarget_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    BalancedCircuit.foldTarget (mapCircuit f L)=(BalancedCircuit.foldTarget L).map f := by
  simp [BalancedCircuit.foldTarget,mapCircuit,mapCleanup]

theorem foldBits_map (f : Wire → Wire) (L : BalancedCircuit.Layout) :
    (BalancedCircuit.foldBits L).map (mapBit f)=BalancedCircuit.foldBits (mapCircuit f L) := by
  simp only [BalancedCircuit.foldBits,List.map_append,List.map_map,List.map_cons,List.map_nil]
  congr 1

theorem offsetBits_map (f : Wire → Wire) (L : BalancedCleanupOffset.Layout) :
    (BalancedCleanupOffset.offsetBits L).map (mapBit f)=BalancedCleanupOffset.offsetBits (mapOffset f L) := by
  simp only [BalancedCleanupOffset.offsetBits,List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : i=1 <;> simp [mapBit,mapOffset,mapCircuit,mapCleanup,h]

theorem wireBlock_map (f w : Wire → Wire) (start len : Nat) :
    (wireBlock w start len).map f=wireBlock (f ∘ w) start len := by
  simp only [wireBlock,List.map_map,Function.comp_def]

theorem sharedPorts_map (f w : Wire → Wire) (sign : Wire) :
    mapCircuit f (balancedSharedPorts w sign)=balancedSharedPorts (f ∘ w) (f sign) := by
  simp only [mapCircuit,mapCleanup,balancedSharedPorts,wireBlock_map,Function.comp_def]

theorem callerCarry_map (f w : Wire → Wire) :
    (OffsetCleanupBorrowedCaller.carry w).map f=OffsetCleanupBorrowedCaller.carry (f ∘ w) := by
  simp [OffsetCleanupBorrowedCaller.carry,wireBlock_map,Function.comp_def]

theorem callerLayout_map (f w : Wire → Wire) (sign : Wire) :
    mapOffset f (OffsetCleanupBorrowedCaller.layout w sign)=
      OffsetCleanupBorrowedCaller.layout (f ∘ w) (f sign) := by
  simp only [mapOffset,mapCircuit,mapCleanup,OffsetCleanupBorrowedCaller.layout,
    balancedSharedPorts,callerCarry_map,wireBlock_map,Function.comp_def]

/-- The source-first seed bit is natural whenever the source is nonempty;
there is no invalid assumption that f maps the default wire0 to wire0. -/
theorem first_source_map (f : Wire → Wire) (xs : List Wire) (h : xs ≠ []) :
    (xs.map f).getD 0 0=f (xs.getD 0 0) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.sharedPorts_map
#print axioms ECDSAAdd.Arithmetic.FieldRename.callerLayout_map
#print axioms ECDSAAdd.Arithmetic.FieldRename.foldBits_map
#print axioms ECDSAAdd.Arithmetic.FieldRename.offsetBits_map
