import ECDSAAdd.Math.SkywalkRails
import ECDSAAdd.Math.SkywalkNat

namespace ECDSAAdd.SkywalkRails

/-- Decode the unsigned smaller magnitude and the gap to the positive larger
rail. The orientation determines which physical rail is smaller. -/
def decode (t : Tick) : SkywalkNat.State :=
  let small := if t.g then t.h.natAbs else t.k.natAbs
  let large := if t.g then t.k else t.h
  ⟨small,(large-(small : Int)).toNat⟩

def railsOf (t : Tick) : State := ⟨t.h,t.k,t.g⟩

def smallerSign (t : Tick) : Bool := if t.g then neg t.h else neg t.k

private theorem signed_neg_abs (x : Int) : signed (neg x) |x|=x := by
  by_cases hn : x<0
  · simp [signed,neg,hn,abs_of_neg hn]
  · have hp : 0≤x := by omega
    simp [signed,neg,hn,abs_of_nonneg hp]

/-- Decoding loses no rail information when the smaller sign is retained.
The retained sign is the actual smaller-rail sign, not the sign-flip tape. -/
theorem frame_reencode (t : Tick) (hf : Frame t) :
    railsOf t=encode t.g (smallerSign t) ((decode t).u : Int) ((decode t).v : Int) := by
  cases hg : t.g
  · have hs : signed (neg t.k) (t.k.natAbs : Int)=t.k := by
      rw [Int.natCast_natAbs]
      exact signed_neg_abs t.k
    have hnonneg : 0≤t.h-(t.k.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      simp only [Frame,hg,Bool.false_eq_true,if_false] at hf
      omega
    have hgap := Int.toNat_of_nonneg hnonneg
    have hsum : (t.k.natAbs : Int)+(t.h-(t.k.natAbs : Int)).toNat=t.h := by
      rw [hgap]
      omega
    simp only [railsOf,encode,smallerSign,decode,hg,Bool.false_eq_true,if_false]
    apply State.ext
    · exact hsum.symm
    · exact hs.symm
    · rfl
  · have hs : signed (neg t.h) (t.h.natAbs : Int)=t.h := by
      rw [Int.natCast_natAbs]
      exact signed_neg_abs t.h
    have hnonneg : 0≤t.k-(t.h.natAbs : Int) := by
      rw [Int.natCast_natAbs]
      simp only [Frame,hg,if_true] at hf
      omega
    have hgap := Int.toNat_of_nonneg hnonneg
    have hsum : (t.h.natAbs : Int)+(t.k-(t.h.natAbs : Int)).toNat=t.k := by
      rw [hgap]
      omega
    simp only [railsOf,encode,smallerSign,decode,hg,if_true]
    apply State.ext
    · exact hs.symm
    · exact hsum.symm
    · rfl

/-- Exact representation bridge to the all-input min-source Stein recurrence.
Signs are retained by the signed tick and only projected out by this theorem. -/
theorem decode_step_encode (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    decode (step (encode g s (z.u : Int) (z.v : Int)))=SkywalkNat.step z := by
  have hun : (0:Int)≤z.u := by omega
  have hvp : (0:Int)<z.v := by omega
  have hvi : (z.v : Int)%2=1 := by omega
  by_cases he : z.u%2=0
  · have hei : (z.u : Int)%2=0 := by omega
    have hhalf : ((z.u/2 : Nat) : Int)=(z.u : Int)/2 := by omega
    have hs : (signed s ((z.u : Int)/2)).natAbs=z.u/2 := by
      have hbase : (((z.u/2 : Nat) : Int)).natAbs=z.u/2 := rfl
      rw [←hhalf]
      cases s with
      | false => exact hbase
      | true => exact (Int.natAbs_neg _).trans hbase
    have hgap : (z.u : Int)/2+(z.v : Int)-((z.u/2 : Nat) : Int)=(z.v : Int) := by
      rw [←hhalf]
      omega
    rw [step_encode_even g s _ _ hun hvp hvi hei]
    simp only [decode,if_true,hs,hgap]
    by_cases hz : z.u=0
    · simp only [SkywalkNat.step,hz,if_true]
      cases z
      simp_all
    · simp [SkywalkNat.step,hz,he]
  · have hei : (z.u : Int)%2≠0 := by omega
    have hzero : z.u≠0 := by omega
    rw [step_encode_odd g s _ _ hun hvp hvi hei]
    by_cases hle : z.v≤z.u
    · let d := (z.u-z.v)/2
      have hd : ((z.u : Int)-(z.v : Int))/2=(d : Int) := by dsimp [d]; omega
      have hn : ((z.v : Int)-(z.u : Int))/2=-(d : Int) := by dsimp [d]; omega
      have hk : (if s then ((z.v : Int)-(z.u : Int))/2 else
          ((z.u : Int)-(z.v : Int))/2).natAbs=d := by
        cases s <;> simp [hd,hn]
      have hgap : ((z.u : Int)+(z.v : Int))/2-(d : Int)=(z.v : Int) := by
        dsimp [d]
        omega
      simp only [decode,Bool.false_eq_true,if_false,hk,hgap]
      simp [SkywalkNat.step,hzero,he,hle,d]
    · let d := (z.v-z.u)/2
      have hd : ((z.v : Int)-(z.u : Int))/2=(d : Int) := by dsimp [d]; omega
      have hn : ((z.u : Int)-(z.v : Int))/2=-(d : Int) := by dsimp [d]; omega
      have hk : (if s then ((z.v : Int)-(z.u : Int))/2 else
          ((z.u : Int)-(z.v : Int))/2).natAbs=d := by
        cases s <;> simp [hd,hn]
      have hgap : ((z.u : Int)+(z.v : Int))/2-(d : Int)=(z.u : Int) := by
        dsimp [d]
        omega
      simp only [decode,Bool.false_eq_true,if_false,hk,hgap]
      simp [SkywalkNat.step,hzero,he,hle,d]

/-- A complete one-step reachability statement, sufficient to reapply the
encoded-rail invariants at every later step. -/
theorem step_reencode (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let t := step (encode g s (z.u : Int) (z.v : Int))
    railsOf t=encode t.g (smallerSign t)
      ((SkywalkNat.step z).u : Int) ((SkywalkNat.step z).v : Int) := by
  dsimp only
  have hf := step_frame g s (z.u : Int) (z.v : Int)
    (by omega) (by omega) (by omega)
  simpa only [decode_step_encode g s z hv hvo] using frame_reencode _ hf

end ECDSAAdd.SkywalkRails
