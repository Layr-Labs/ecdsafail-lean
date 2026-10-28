import ECDSAAdd.Arithmetic.ZeroControl
import ECDSAAdd.Arithmetic.Constant

namespace ECDSAAdd.Arithmetic

private theorem zeroBit_count (bs : List ZeroBit) (w : Wire) :
    (bs.flatMap ZeroBit.wires).count w =
      (bs.map ZeroBit.input).count w + (bs.map ZeroBit.work).count w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,ZeroBit.wires,List.map_cons,List.count_append,
      List.count_cons,List.count_nil,ih]
    omega

/-- 保留输入，XOR 写入 control ∧ (input = k)；同一组零检测工作位前后均为零。 -/
def equalConstant (control target : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  xorConstant (bs.map ZeroBit.input) k ++ zeroControlled control target bs ++
    xorConstant (bs.map ZeroBit.input) k

theorem equalConstant_correct (control target : Wire) (bs : List ZeroBit) (k : Nat)
    (hnd : (control::target::bs.flatMap ZeroBit.wires).Nodup) (hk : k<2^bs.length)
    (s : State) (m : List Bool) (hz : ∀ b∈bs,s.basis b.work=false) :
    run (equalConstant control target bs k) m s =
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ (s.basis control && decide (regValue (bs.map ZeroBit.input) s.basis=k)))⟩ := by
  let src := bs.map ZeroBit.input
  have hsrc : src.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hb : src.count w ≤ (bs.flatMap ZeroBit.wires).count w := by
      rw [zeroBit_count]; exact Nat.le_add_right _ _
    have hh := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons] at hh
    omega
  have hin (b : ZeroBit) (hb : b∈bs) : b.input∈bs.flatMap ZeroBit.wires :=
    List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have hwork (b : ZeroBit) (hb : b∈bs) : b.work∉src := by
    intro hi
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
    have hni := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    have hdup : 2≤(bs.flatMap ZeroBit.wires).count b.work := by
      have hwc : 1≤(bs.map ZeroBit.work).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩)
      have hic : 1≤(bs.map ZeroBit.input).count b.work := List.count_pos_iff.mpr (List.mem_map.mpr ⟨a,ha,he⟩)
      have hc := zeroBit_count bs b.work
      omega
    have hh := List.nodup_iff_count.mp hni b.work
    omega
  have hc : control∉src := by
    intro h; obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ (he ▸ hin b hb))
  have ht : target∉src := by
    intro h; obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (he ▸ hin b hb)
  let u := run (xorConstant src k) m s
  obtain ⟨hup,hue,huv⟩ := xorConstant_correct src hsrc k (by simpa [src] using hk) s m
  have huz : ∀ b∈bs,u.basis b.work=false := fun b hb => (hue _ (hwork b hb)).trans (hz b hb)
  have hh := zeroControlled_correct control target bs hnd u m huz
  have hall : bs.all (fun b => !u.basis b.input) = decide (regValue src s.basis=k) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    simp only [Bool.not_eq_true']
    have heq : (∀ b∈bs,u.basis b.input=false) ↔ regValue src u.basis=0 := by
      rw [regValue_zero]
      simp [src]
    rw [heq]
    change (regValue src u.basis=0) ↔ decide (regValue src s.basis=k)=true
    rw [show regValue src u.basis=regValue src s.basis ^^^ k from huv]
    simp
  let v : State := ⟨s.phase,writeBit u.basis target
    (s.basis target ^^ (s.basis control && decide (regValue src s.basis=k)))⟩
  have hv : run (zeroControlled control target bs) m u=v := by
    rw [hh,hall]
    dsimp [v]
    rw [show u.phase=s.phase from hup,show u.basis target=s.basis target from hue _ ht,
      show u.basis control=s.basis control from hue _ hc]
  obtain ⟨hvp,hve,hvv⟩ := xorConstant_correct src hsrc k (by simpa [src] using hk) v (m.drop bs.length)
  have hvs : regValue src v.basis=regValue src u.basis := by
    apply regValue_congr
    intro w hw
    simp [v,writeBit,show w≠target from fun h => ht (h ▸ hw)]
  have hrestore : regValue src (run (xorConstant src k) (m.drop bs.length) v).basis=regValue src s.basis := by
    rw [hvv,hvs,show regValue src u.basis=regValue src s.basis ^^^ k from huv,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  rw [equalConstant,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(xorConstant_counts _ _).2,
    (zeroControlled_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  change run (xorConstant src k) (m.drop bs.length) (run (zeroControlled control target bs) m u)=_
  rw [hv]
  apply (show ∀ a b : State, a.phase=b.phase → a.basis=b.basis → a=b from
    fun ⟨ap,ab⟩ ⟨bp,bb⟩ hp hb => by cases hp; cases hb; rfl)
  · exact hvp
  · funext w
    by_cases hw : w∈src
    · rw [(regValue_eq_iff src _ _).mp hrestore w hw]
      simp [writeBit,show w≠target from fun h => ht (h ▸ hw)]
    · rw [hve w hw]
      dsimp [v]
      by_cases hwt : w=target
      · subst w; simp [writeBit,src]
      · simp [writeBit,hwt,show u.basis w=s.basis w from hue w hw]

theorem equalConstant_counts (control target : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (equalConstant control target bs k)=bs.length ∧
    measurementCount (equalConstant control target bs k)=bs.length := by
  simp only [equalConstant,toffoliCount_append,measurementCount_append,
    (xorConstant_counts _ _).1,(xorConstant_counts _ _).2,
    (zeroControlled_counts _ _ _).1,(zeroControlled_counts _ _ _).2,Nat.zero_add,Nat.add_zero,and_self]

/-- 常量的取值不改变实际支持：零检测本身已经触及全部布局线。 -/
theorem equalConstant_wires (control target : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (equalConstant control target bs k) =
      (control::target::bs.flatMap ZeroBit.wires).toFinset := by
  have hsub : wires (xorConstant (bs.map ZeroBit.input) k) ⊆
      (control::target::bs.flatMap ZeroBit.wires).toFinset := by
    intro w hw
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp
      (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hw))
    simp only [List.mem_toFinset,List.mem_cons]
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))
  rw [equalConstant,wires_append,wires_append,zeroControlled_wires,
    Finset.union_eq_right.mpr hsub,Finset.union_eq_left.mpr hsub]

end ECDSAAdd.Arithmetic
