import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowBounds

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem shadow_odd_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) :
    (Shadow.reduced b 15 z).v%2=1 := by
  by_cases f : Shadow.far b 15 z
  · exact shadow_odd b z (small f) odd
  · simpa [Shadow.reduced,f] using odd

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem true_records_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S:Bool) :
    let T:=Shadow.reduced b 15 z
    SkywalkTrace.trace 15 (encode G S T.u T.v)=SkywalkTrace.trace 15 (encode G S z.u z.v) := by
  by_cases f : Shadow.far b 15 z
  · exact true_records b z (small f) odd G S
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem interrupted_row_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S cross:Bool)
    (cells:List (Bool×Bool))
    (records:let T:=Shadow.reduced b 15 z
      cells=SkywalkTrace.trace 15 (encode G S T.u T.v)) :
    let far:=decide (Shadow.far b 15 z)
    let u:=far && afterFlags (decide (z.v<z.u)) (cells.take 5)
    ∃row<63145,∀q<23,(rawCol q).testBit row=rawBit (read (cells.drop 5)) far u (far && cross) q := by
  rw [records.trans (true_records_shadow7 b z small odd G S)]
  by_cases f:Shadow.far b 15 z
  · simpa only [f,decide_true,Bool.true_and] using
      far_suffix 5 (Shadow.represented _ _ _ (small f) f).1 G S cross (by omega) odd
  · simpa only [f,decide_false,Bool.false_and] using near_suffix 5 z G S (by omega) odd

end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.SharedSigned
open SkywalkRails IntegerHigh
set_option maxHeartbeats 2500000

theorem same_shadow7 (b:Nat) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (odd:z.v%2=1) (G S:Bool) :
    let t:=Shadow.reduced b 15 z
    let pair:=flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
    SkywalkTrace.next^[15] (encode G S z.u z.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v:=by
  have shadow:=lift 15 G S (Shadow.reduced b 15 z) (shadow_odd_shadow7 b z small odd)
  rw [true_records_shadow7 b z small odd G S] at shadow
  exact ⟨shadow,lift _ _ _ _ odd⟩

end ECDSAAdd.Entrant.StairPacket.SharedSigned

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem advance_signed_gen_shadow7 (i b x p:Nat) (lo:15≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw history:State) (dom:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (small : Shadow7.SmallIfFar b 15 (unsigned i x p)) :
    let z:=unsigned i x p
    let t:=Shadow.reduced b 15 z
    let flags:=SharedSigned.flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    let endState:=unsigned (i+15) x p
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode flags.1 flags.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
      InputAt (i+15) (encode flags.1 flags.2 endState.u endState.v) (endRaw i raw history):=by
  let z:=unsigned i x p
  have odd:z.v%2=1:=(SkywalkNat.iter_valid i (SkywalkNat.init x p) good.positive good.odd).2.1
  obtain ⟨a,b'⟩:=SharedSigned.same_shadow7 b z small odd G S
  have eq:=unique_input input (fixed_input i x p (by omega) good raw dom)
  have stepRel:canonical (i+15) x p=SkywalkTrace.next^[15] (canonical i x p):=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have numRel:unsigned (i+15) x p=SkywalkNat.step^[15] z:=by rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  have nextDom:=advance_gen i x p lo (by omega) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw history dom
  have active:=fixed_input (i+15) x p hi good (endRaw i raw history) nextDom
  dsimp only
  refine ⟨a,?_⟩
  rw [stepRel,←eq,b'] at active
  simpa only [numRel] using active

end ECDSAAdd.Entrant.StairPacket.WideReference

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 25000
attribute [local irreducible] run SkywalkNat.step

theorem stepInput_gen_shadow7 (i b x p:Nat) (lo:15 ≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw v:State) (g sg:Bool) (domain:Domain i x p raw) (input:InputAt i (signedAt i x p g sg) raw)
    (small : Shadow7.SmallIfFar b 15 (unsigned i x p)) :
    let next:=SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt i x p g sg))
    Domain (i+15) x p (endRaw i raw v) ∧ InputAt (i+15) (signedAt (i+15) x p next.1 next.2) (endRaw i raw v) := by
  exact ⟨advance_gen i x p lo (Nat.le_of_lt hi) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw v domain,
    (advance_signed_gen_shadow7 i b x p lo hi good raw v domain g sg input small).2⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open IntegerHigh SkywalkNat Shadow HighBankSum

theorem trueControls_shadow7 (b w : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z)
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
    have val:=LeaveShadowRails.far_result b w z (small f) f odd room
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
        have rails:=(LeaveShadowRails.rail b z (small f) f).2 h
        rw [par]
        have eq : reduced b 15 z=⟨z.u,(reduced b 15 z).v⟩:=SkywalkNat.State.ext rails.1 rfl
        have g:=rails.2.2
        rw [rails.1] at g
        rw [eq,lead_wait 15 _ _ g,idx,place,if_neg (Nat.not_le.mpr h)]) ,side,par]
  · simp [actualMode,farMode,ofFlags,enabled,crossing,Expr.read,f]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem afterThreshold_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (e:Nat) (en:e≤1) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    (2^b≤full.u-e ↔ 2^b≤r.u-e) ∧ (0<full.u ↔ 0<r.u) := by
  by_cases f : Shadow.far b 15 z
  · exact afterThreshold b z (small f) e en
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem limbGaps_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    ∃a c:Nat,full.u=r.u+2^(b+1)*a ∧ full.v=r.v+2^(b+1)*c := by
  by_cases f : Shadow.far b 15 z
  · exact limbGaps b z (small f)
  · exact ⟨0, 0, by simp [Shadow.reduced,f], by simp [Shadow.reduced,f]⟩

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem retainedLow_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=PortalValues.negative sg r.u
    let V:=2^(b+1)
    PortalValues.negative sg F.u=e ∧ (F.u+F.v)%V=(r.u+r.v)%V ∧ (F.u-e.toNat)%V=(r.u-e.toNat)%V := by
  by_cases f : Shadow.far b 15 z
  · exact retainedLow b z (small f) sg
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
open SkywalkNat Shadow LeaveCompanion PortalValues
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem truth_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    (decide (2^b≤r.u-e)=decide (2^b≤F.u-e)) ∧
      upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e ∧
      (F.u-e)%(2*2^b)=(r.u-e)%(2*2^b) ∧
      negative sg F.u=negative sg r.u := by
  by_cases f : Shadow.far b 15 z
  · exact truth b z (small f) sg
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat Shadow HighBankSum

theorem inputFit_shadow7 (b : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (endSmall : Shadow7.EndSmall b z) :
    let a:=step^[15] (reduced b 15 z)
    min a.u a.v<2^b ∧ (a.u+a.v)/2^b<2^19 := by
  by_cases f : far b 15 z
  · exact inputFit b z (small f)
  · simp only [reduced,if_neg f]
    refine ⟨endSmall,?_⟩
    have upper : z.u+z.v < 3*limb b 15 :=
      (Nat.div_lt_iff_lt_mul (by unfold limb; positivity)).mp (Nat.lt_of_not_ge f)
    have noninc := iter_sum_nonincrease 15 z
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr
    rw [scale,pow_succ] at upper
    omega

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

namespace ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
open SkywalkNat Shadow LeaveCompanion PortalValues
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem restored_shadow7 (b k : Nat) (z : SkywalkNat.State) (small : Shadow7.SmallIfFar b 15 z) (endSmall : Shadow7.EndSmall b z) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k =
      ((F.u-e)/2^(b+1))%2^k := by
  let F:=step^[15] z
  let r:=step^[15] (reduced b 15 z)
  let e:=(negative sg r.u).toNat
  have le:e≤1 := by cases h:negative sg r.u <;> simp [e,h]
  have eq:=truth_shadow7 b z small sg
  have pos:0<F.u ↔ 0<r.u := (LeaveShadowRails.afterThreshold_shadow7 b z small e le).2
  have eu:e≤F.u := by
    by_cases h:0<F.u
    · omega
    · have no:¬0<r.u:=fun hr=>h (pos.mpr hr)
      simp [e,negative,no]
  have sm:min F.u F.v<2^b := endSmall
  have out:=upper_restore (2^b) F.u F.v e (2^k) (Nat.two_pow_pos _) le eu sm (Nat.two_pow_pos _)
  have h:2^b≤r.u-e ↔ 2^b≤F.u-e := (LeaveShadowRails.afterThreshold_shadow7 b z small e le).1.symm
  have two : 2*2^b=2^(b+1) := (Nat.mul_comm _ _).trans (pow_succ 2 b).symm
  change ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k=_
  have bor : upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e := eq.2.1
  simp only [h,bor]
  simpa only [two] using out

end ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
