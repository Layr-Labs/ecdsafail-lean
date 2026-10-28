import ECDSAAdd.Arithmetic.BalancedCleanupOffsetLayout
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetMath
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
open BalancedField

/-- Actual unnormalized Clifford view. The result remains an unsigned
double magnitude; only the source receives the signed comparison bias. -/
theorem view_value (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=(magnitude R).toNat)
    (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hL : s.basis L.lower=negative R) :
    let t := run (view L) m s
    regValue L.r t.basis=rawR B R ∧ regValue L.y t.basis=biasedY B R Y ∧
    (∀q,q∉L.r → q∉L.y → t.basis q=s.basis q) := by
  let U := (magnitude R).toNat
  let v1 := run (rotateLeft L.r) m s
  let ins : Program := [.X L.r0,.CX L.sign L.r0,.CX L.lower L.r0]
  let v2 := run ins m v1
  let v3 := run (signComplement L.sign L.y) m v2
  let v4 := run (signComplement L.lower L.y) m v3
  let v5 := run [.X L.ymsb] m v4
  have w := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have d := List.nodup_append'.mp (BalancedCleanup.Layout.dataND _ (L.cleanupND hn))
  have dr := d.1
  have dy := (List.nodup_append'.mp d.2.1).1
  have dis := d.2.2
  have away (q : Wire) (hq : q∈[L.sign,L.lower]) : q∉L.r ∧ q∉L.y := by
    have a := L.flagAway hn q (by simp only [List.mem_cons] at hq ⊢; tauto)
    exact ⟨fun h => a (by simp [h]),fun h => a (by simp [h])⟩
  have r0R : L.r0∈L.r := by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
  have ymY : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
  have r0Y : L.r0∉L.y := fun h => List.disjoint_left.mp dis r0R (by simp [h])
  have ymR : L.ymsb∉L.r := fun h => List.disjoint_left.mp dis h (by simp [ymY])
  have sr : L.sign≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have lr : L.lower≠L.r0 := fun e => (away _ (by simp)).1 (e ▸ r0R)
  have rot0 := rotateLeft_spec L.r dr U (by
    have b := magnitude_bounds R hr
    have c := BalancedField.constants
    have u := Int.toNat_of_nonneg b.1
    rw [w.2.1]
    norm_num only [Nat.reducePow] at c ⊢
    omega) s m hR
  have rot := rot0.2
  have rotfr := (rotate_frame L.r s m).2.2.2
  have S1 : v1.basis L.sign=B := (rotfr _ (away _ (by simp)).1).trans hS
  have L1 : v1.basis L.lower=negative R := (rotfr _ (away _ (by simp)).1).trans hL
  have low0 : v1.basis L.r0=false := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    cases e : v1.basis L.r0
    · rfl
    · simp [e] at rot
      omega
  have tail1 : regValue (L.rtail++[L.rmsb]) v1.basis=U := by
    change (if v1.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v1.basis=2*U at rot
    rw [low0] at rot
    simp only [Bool.false_eq_true,if_false,zero_add] at rot
    omega
  have I2 : v2.basis L.r0=!(B ^^ negative R) := by
    cases b : B <;> cases l : negative R <;> simp [v2,ins,run,writeBit,sr,lr,S1,L1,low0,b,l]
  have out2 (q : Wire) (hq : q≠L.r0) : v2.basis q=v1.basis q := by simp [v2,ins,run,writeBit,hq]
  have S2 : v2.basis L.sign=B := (out2 _ sr).trans S1
  have L2 : v2.basis L.lower=negative R := (out2 _ lr).trans L1
  have tailAway : L.r0∉L.rtail++[L.rmsb] := (List.nodup_cons.mp dr).1
  have R2 : regValue L.r v2.basis=rawR B R := by
    change (if v2.basis L.r0 then 1 else 0)+2*regValue (L.rtail++[L.rmsb]) v2.basis=_
    rw [regValue_congr _ _ _ (fun q hq => out2 q (fun e => tailAway (e ▸ hq))),tail1,I2]
    cases e : !(B ^^ negative R) <;> simp [rawR,U,e,Nat.add_comm]
  have Y2 : regValue L.y v2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => (out2 q (fun e => r0Y (e ▸ hq))).trans
      (rotfr q (fun hrq => List.disjoint_left.mp dis hrq (by simp [hq]))))).trans hY
  have cS := signComplement_correct L.sign L.y dy (away _ (by simp)).2 v2 m
  have cL := signComplement_correct L.lower L.y dy (away _ (by simp)).2 v3 m
  have L3 : v3.basis L.lower=negative R := (cS.2.1 _ (away _ (by simp)).2).trans L2
  have R4 : regValue L.r v4.basis=rawR B R := by
    exact (regValue_congr _ _ _ (fun q hq => (cL.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))).trans (cS.2.1 q
      (fun hyq => List.disjoint_left.mp dis hq (by simp [hyq]))))).trans R2
  have Y4 : regValue L.y v4.basis=encodeWord 256 (viewedY B R Y) := by
    rw [cL.2.2,cS.2.2,L3,S2,Y2,w.2.2.1]
    have hb := encodeWord_bound 256 Y
    have comp := BalancedCleanup.complement_encoded Y
    cases B <;> cases l : negative R <;> simp [viewedY,l] <;> omega
  have bvY := BalancedCleanup.bias_value L.ylow L.ymsb dy v4 m
  rw [hw.1.2.1] at bvY
  change (regValue L.y v5.basis : Int)=signedDecode 256 (regValue L.y v4.basis)+((2^255 : Nat) : Int) at bvY
  rw [Y4,(comparison_words_decode B R Y hr hy).2] at bvY
  have Y5 : regValue L.y v5.basis=biasedY B R Y := by
    have bv := biasedY_cast B R Y hr hy
    omega
  have R5 : regValue L.r v5.basis=rawR B R :=
    (regValue_congr _ _ _ (fun q hq => by simp [v5,run,writeBit,show q≠L.ymsb from fun e => ymR (e ▸ hq)])).trans R4
  have emptyRot (t : State) : run (rotateLeft L.r) (m.take 0) t=run (rotateLeft L.r) m t := by
    simpa only [(rotate_counts L.r).2.2.2] using run_take (rotateLeft L.r) m t
  have emptyS (t : State) : run (signComplement L.sign L.y) (m.take 0) t=run (signComplement L.sign L.y) m t := by
    simpa only [(signComplement_counts L.sign L.y).2] using run_take (signComplement L.sign L.y) m t
  have emptyL (t : State) : run (signComplement L.lower L.y) (m.take 0) t=run (signComplement L.lower L.y) m t := by
    simpa only [(signComplement_counts L.lower L.y).2] using run_take (signComplement L.lower L.y) m t
  have execute : run (view L) m s=v5 := by
    simp only [view,List.append_assoc,run_append,
      (rotate_counts L.r).2.2.2,(signComplement_counts L.sign L.y).2,
      (signComplement_counts L.lower L.y).2,measurementCount,List.drop_zero,emptyRot,emptyS,emptyL]
    rfl
  rw [execute]
  refine ⟨R5,Y5,?_⟩
  intro q qr qy
  have nr : q≠L.r0 := fun e => qr (e ▸ r0R)
  have ny : q≠L.ymsb := fun e => qy (e ▸ ymY)
  have v5q : v5.basis q=v4.basis q := by simp [v5,run,writeBit,ny]
  exact v5q.trans ((cL.2.1 q qy).trans ((cS.2.1 q qy).trans ((out2 q nr).trans (rotfr q qr))))

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.view_value
