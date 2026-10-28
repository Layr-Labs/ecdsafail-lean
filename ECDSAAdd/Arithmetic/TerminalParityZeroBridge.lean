import ECDSAAdd.Arithmetic.TerminalParityZeroHead

set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace ECDSAAdd.Arithmetic.TerminalParityZeroHead
open BalancedCleanupOffset

/-- The matching flag follows from the old block's guaranteed zero output.
No new arithmetic-domain premise is imposed on the surrounding caller. -/
theorem eq_old_of_clears (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire)
    (hn : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (mOld mNew : List Bool) (hz : s.basis cinC=false) (hzD : s.basis d=false)
    (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (hclear : (run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds
      a y cinC cinB d target) mOld s).basis target=false)
    (hnonempty : ys≠[]) :
    run (program bits xs ys cs ds a y cinC cinB d target) mNew s=
      run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds
        a y cinC cinB d target) mOld s := by
  let D := decision (false::bits.map (fun b => b.value s.basis))
    (s.basis a::xs.map s.basis) (s.basis y::ys.map s.basis) false (s.basis cinB)
  have old := BalancedCleanupOffsetZeroHead.run_correct bits xs ys cs ds a y cinC cinB
    d target hn ha hb hx hc hd s mOld hz hzD hcc hdd
  change run (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds a y cinC cinB
    d target) mOld s=⟨s.phase,writeBit s.basis target (s.basis target ^^ D)⟩ at old
  have bit := congrArg (fun t : State => t.basis target) old
  have cleared : (s.basis target ^^ D)=false := by
    simpa only [writeBit,Function.update_self,hclear] using bit.symm
  have tag : s.basis target=D := by
    cases hp : s.basis target <;> cases hD : D <;> simp_all
  have fresh := run_correct bits xs ys cs ds a y cinC cinB d target hn ha hb hx hc hd
    s mNew hz hzD hcc hdd tag hnonempty
  rw [fresh,old,tag,Bool.xor_self]

end ECDSAAdd.Arithmetic.TerminalParityZeroHead
#print axioms ECDSAAdd.Arithmetic.TerminalParityZeroHead.eq_old_of_clears
