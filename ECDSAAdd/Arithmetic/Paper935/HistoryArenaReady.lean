import ECDSAAdd.Arithmetic.Paper935.StorePush
import ECDSAAdd.Arithmetic.Paper935.Arena

namespace ECDSAAdd.Arithmetic.Paper935

theorem storePushForget_frame_arena (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hpush : (output::port::record).Nodup) (houtzero : s.basis output=false)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hstable : List.Disjoint (port::record)
      ([one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires))
    (hfit : (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0))=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (ordinal : Nat) :
    let t := runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s
    (∀ q,q∉port::record → t.basis q=s.basis q) ∧
    (∀ A : Arena,(port::record).toFinset⊆A.live → A.Ready s.basis → A.Ready t.basis) := by
  have hs := storePush_spec one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
  have ht := storePushForget_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal
  dsimp only at ht ⊢
  have keep (q : Wire) (away : q∉port::record) :
      (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis q=s.basis q := by
    rw [ht]
    have hp : q≠port := fun he => away (by simp [he])
    exact (Function.update_of_ne hp _ _).trans (hs.2.2.2.2 q away)
  refine ⟨keep,?_⟩
  intro A owned ready q inside free
  rw [keep q (fun hq => free (owned (List.mem_toFinset.mpr hq)))]
  exact ready q inside free

end ECDSAAdd.Arithmetic.Paper935
