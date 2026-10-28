import ECDSAAdd.Arithmetic.Paper935.FoldBlockModel
import ECDSAAdd.Arithmetic.RippleAdder

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem block_geometry (control : Wire) (b : FoldCell) (rest : List FoldCell)
    (cin : Option Wire) (hn : (control::cin.toList++(b::rest).flatMap FoldCell.wires).Nodup) :
    ([control,b.data,b.carry]++cin.toList).Nodup ∧
    (control::(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup ∧
    List.Disjoint ([control,b.data,b.carry]++cin.toList) (rest.flatMap FoldCell.wires) := by
  have localNd : ([control,b.data,b.carry]++cin.toList).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have nextCount (q : Wire) : (b.next cin).toList.count q ≤ cin.toList.count q+[b.carry].count q := by
    cases cin <;> cases hb : b.literal <;> simp [FoldCell.next,hb]
  have tailNd : (control::(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have hnext := nextCount q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hnext ⊢
    omega
  refine ⟨localNd,tailNd,?_⟩
  apply List.disjoint_left.mpr
  intro q hq hr
  have h := List.nodup_iff_count.mp hn q
  have hc := List.count_pos_iff.mpr hq
  have ht := List.count_pos_iff.mpr hr
  simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hc
  omega

/-- Execution of an author carry block equals its Boolean carry model on every
measurement tape, including the phase. Only carry targets must start clean. -/
theorem foldBlock_run (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    run (foldBlock control cells cin sums keep) m s=
      ⟨s.phase,foldBlockModel control cells cin sums keep s.basis⟩ := by
  induction cells generalizing cin s m with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,apart⟩ := block_geometry control b rest cin hn
    let prepared := writeBit (writeBit s.basis b.carry
      (carryBit (s.basis b.data) (b.literal && s.basis control) ((cin.map s.basis).getD false)))
      b.data (s.basis b.data ^^ (b.literal && (cin.map s.basis).getD false))
    let tail := foldBlockModel control rest (b.next cin) sums keep prepared
    have outside (q : Wire) (hq : q∈[control,b.data,b.carry]++cin.toList) :
        q∉rest.flatMap FoldCell.wires := List.disjoint_left.mp apart hq
    have frame (q : Wire) (hq : q∈[control,b.data,b.carry]++cin.toList) : tail q=prepared q :=
      foldBlockModel_frame control rest (b.next cin) sums keep prepared q (outside q hq)
    have localClean := clean b (by simp)
    have nextClean : ∀ c∈rest,prepared c.carry=false := by
      intro c hc
      have mem : c.carry∈rest.flatMap FoldCell.wires := by
        exact List.mem_flatMap.mpr ⟨c,hc,by simp [FoldCell.wires]⟩
      have hd : c.carry≠b.data := by intro e; exact outside b.data (by simp) (e ▸ mem)
      have ht : c.carry≠b.carry := by intro e; exact outside b.carry (by simp) (e ▸ mem)
      simpa [prepared,writeBit,hd,ht] using clean c (by simp [hc])
    have nd : [control,b.data,b.carry].Nodup := (List.nodup_append.mp localNd).1
    have hcd : control≠b.data := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.1
    have hct : control≠b.carry := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.2
    have hdt : b.data≠b.carry := by
      simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    have ctrl : tail control=s.basis control := by rw [frame control (by simp)]; simp [prepared,writeBit,hcd,hct]
    have inp : (cin.map tail).getD false=(cin.map s.basis).getD false := by
      cases hi : cin with
      | none => rfl
      | some d =>
        have dis := (List.nodup_append'.mp localNd).2.2
        have dd : d≠b.data := by
          intro e; subst d
          exact List.disjoint_left.mp dis (show b.data∈[control,b.data,b.carry] by simp) (by simp [hi])
        have dt : d≠b.carry := by
          intro e; subst d
          exact List.disjoint_left.mp dis (show b.carry∈[control,b.data,b.carry] by simp) (by simp [hi])
        simp only [Option.map_some,Option.getD_some]
        rw [frame d (by simp [hi])]
        simp [prepared,writeBit,dd,dt]
    have dressed : tail b.data=(s.basis b.data ^^ (b.literal && (cin.map tail).getD false)) := by
      rw [frame b.data (by simp),inp]
      simp [prepared,writeBit]
    have carry : tail b.carry=carryBit (s.basis b.data) (b.literal && tail control) ((cin.map tail).getD false) := by
      rw [frame b.carry (by simp),ctrl,inp]
      simp [prepared,writeBit,Ne.symm hdt]
    rw [foldBlock,run_append,run_take,run_append,run_take,
      foldCarryForward_run b.literal control b.data b.carry cin localNd s m localClean,
      (foldCarryForward_counts b.literal control b.data b.carry cin).2,List.drop_zero]
    rw [ih (b.next cin) tailNd ⟨s.phase,prepared⟩ m nextClean]
    rw [foldCarryBackward_run b.literal control b.data b.carry cin sums (keep && rest.isEmpty)
      localNd ⟨s.phase,tail⟩ _ (s.basis b.data) dressed carry]
    simp only [ctrl,inp]
    rw [carry,ctrl,inp]
    rfl

def foldBlockLiteral : List FoldCell → Bool → Nat
  | [],_ => 0
  | b::rest,enabled => (b.literal && enabled).toNat+2*foldBlockLiteral rest enabled

/-- The independent Boolean model writes the low word of controlled literal
addition, including an optional incoming carry. -/
theorem foldBlockModel_value (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (keep : Bool) (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : BasisState) :
    regValue (cells.map FoldCell.data) (foldBlockModel control cells cin true keep s)=
      (regValue (cells.map FoldCell.data) s+foldBlockLiteral cells (s control)+
        ((cin.map s).getD false).toNat)%2^cells.length := by
  induction cells generalizing cin s with
  | nil => simp [foldBlockModel,regValue,foldBlockLiteral,Nat.mod_one]
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,apart⟩ := block_geometry control b rest cin hn
    let input := (cin.map s).getD false
    let outCarry := carryBit (s b.data) (b.literal && s control) input
    let prepared := writeBit (writeBit s b.carry outCarry) b.data (s b.data ^^ (b.literal && input))
    let tail := foldBlockModel control rest (b.next cin) true keep prepared
    have outside (q : Wire) (hq : q∈[control,b.data,b.carry]++cin.toList) :
        q∉rest.flatMap FoldCell.wires := List.disjoint_left.mp apart hq
    have away (q : Wire) (hq : q∈rest.map FoldCell.data) : q≠b.data ∧ q≠b.carry := by
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
      have mem : c.data∈rest.flatMap FoldCell.wires := List.mem_flatMap.mpr ⟨c,hc,by simp [FoldCell.wires]⟩
      constructor
      · intro e; exact outside b.data (by simp) (e ▸ mem)
      · intro e; exact outside b.carry (by simp) (e ▸ mem)
    have nd : [control,b.data,b.carry].Nodup := (List.nodup_append.mp localNd).1
    have hcd : control≠b.data := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.1
    have hct : control≠b.carry := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.2
    have hdt : b.data≠b.carry := by
      simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    have ctrl : prepared control=s control := by simp [prepared,writeBit,hcd,hct]
    have next : ((b.next cin).map prepared).getD false=outCarry := by
      cases hi : cin <;> cases hb : b.literal <;>
        simp [FoldCell.next,hb,prepared,writeBit,Ne.symm hdt,outCarry,input,hi,carryBit]
    have before : regValue (rest.map FoldCell.data) prepared=regValue (rest.map FoldCell.data) s := by
      apply regValue_congr
      intro q hq
      obtain ⟨hd,ht⟩ := away q hq
      simp [prepared,writeBit,hd,ht]
    have after : regValue (rest.map FoldCell.data)
        (foldBlockModel control (b::rest) cin true keep s)=regValue (rest.map FoldCell.data) tail := by
      apply regValue_congr
      intro q hq
      obtain ⟨hd,ht⟩ := away q hq
      simp [foldBlockModel,tail,prepared,outCarry,input,writeBit,hd,ht]
    have head : foldBlockModel control (b::rest) cin true keep s b.data=
        sumBit (s b.data) (b.literal && s control) input := by simp [foldBlockModel,writeBit,input]
    have tailValue := ih (b.next cin) tailNd prepared
    rw [ctrl,next,before] at tailValue
    have valueCons (q : Wire) (qs : List Wire) (v : BasisState) :
        regValue (q::qs) v=(v q).toNat+2*regValue qs v := by
      simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite]
    change regValue (b.data::rest.map FoldCell.data) _=_
    rw [valueCons,head,after]
    rw [show regValue (rest.map FoldCell.data) tail=_ from tailValue]
    simpa only [List.map_cons,valueCons,foldBlockLiteral,List.length_cons] using
      sum_value_step (s b.data) (b.literal && s control) input
        (regValue (rest.map FoldCell.data) s) (foldBlockLiteral rest (s control)) rest.length

/-- Integer output of the actual measured carry block. -/
theorem foldBlock_run_value (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (keep : Bool) (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    regValue (cells.map FoldCell.data) (run (foldBlock control cells cin true keep) m s).basis=
      (regValue (cells.map FoldCell.data) s.basis+foldBlockLiteral cells (s.basis control)+
        ((cin.map s.basis).getD false).toNat)%2^cells.length := by
  rw [foldBlock_run control cells cin true keep hn s m clean]
  exact foldBlockModel_value control cells cin keep hn s.basis

end ECDSAAdd.Arithmetic.Paper935
