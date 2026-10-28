import ECDSAAdd.Arithmetic.Paper935.WindowRoutedPhysical

namespace ECDSAAdd.Arithmetic.Paper935

/-- A decidable presentation of the public row-stage wiring obligations. -/
def routedStaticCheck (L : RoutedBankLayout) : Prop :=
  (L.q::L.parity::L.u::L.k::(L.f.wires++(L.glow::(L.gmid++[L.gsign])))).Nodup ∧
  (L.q::L.parity::L.u::L.k::((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)).Nodup ∧
  (L.glow::(L.gmid++[L.gsign])).Nodup ∧
  (L.active::L.vlow::(L.vmid++[L.vsign])).Nodup ∧
  List.Disjoint (L.glow::(L.gmid++[L.gsign])) ((L.vlow::(L.vmid++[L.vsign]))++L.gv.wires) ∧
  List.Disjoint (L.vlow::(L.vmid++[L.vsign])) ((L.glow::(L.gmid++[L.gsign]))++L.gv.wires) ∧
  L.active∉(L.glow::(L.gmid++[L.gsign]))++L.gv.wires ∧
  L.f.wires.length=L.gmid.length+2 ∧ L.gv.wires.length=L.vmid.length+2 ∧
  (L.q::((L.f.wires++(L.vlow::(L.vmid++[L.vsign])))++((L.glow::(L.gmid++[L.gsign]))++L.gv.wires))).Nodup ∧
  List.Disjoint [L.q,L.parity,L.u,L.k,L.active]
    (L.f.wires++(L.vlow::(L.vmid++[L.vsign]))++(L.glow::(L.gmid++[L.gsign]))++L.gv.wires) ∧
  List.Disjoint L.f.wires ((L.glow::(L.gmid++[L.gsign]))++(L.vlow::(L.vmid++[L.vsign]))++L.gv.wires)

theorem routedStaticCheck_iff (L : RoutedBankLayout) : routedStaticCheck L ↔ L.Valid := by
  constructor
  · rintro ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩
    exact ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩
  · intro h
    exact ⟨h.addFG,h.addV,h.half,h.double,h.gSep,h.vSep,h.activeSep,h.fgLength,h.vLength,h.route,h.controls,h.fSep⟩

instance routedValidDecidable (L : RoutedBankLayout) : Decidable L.Valid :=
  have : Decidable (routedStaticCheck L) := by unfold routedStaticCheck List.Disjoint; infer_instance
  decidable_of_iff (routedStaticCheck L) (routedStaticCheck_iff L)

/-- Row views come directly from the allocated bank, including both sign
addresses. Empty payloads and illegal aliasing return an explicit failure. -/
def compileRoutedBank (q parity u k active : Wire) (b : WindowBank) : Option RoutedBankLayout :=
  match b.g.payload,b.fv.payload with
  | glow::gmid,vlow::vmid =>
    let L : RoutedBankLayout := ⟨q,parity,u,k,active,b.f,b.gv,glow,gmid,b.g.sign,vlow,vmid,b.fv.sign⟩
    if L.Valid then some L else none
  | _,_ => none

theorem compileRoutedBank_contract (q parity u k active : Wire) (b : WindowBank)
    (L : RoutedBankLayout) (h : compileRoutedBank q parity u k active b=some L) :
    L.Valid ∧ L.before=b ∧ L.q=q ∧ L.parity=parity ∧ L.u=u ∧ L.k=k ∧ L.active=active := by
  rcases b with ⟨f,⟨gs,gsgn⟩,⟨vs,vsgn⟩,gv⟩
  cases gs with
  | nil => simp [compileRoutedBank] at h
  | cons glow gmid =>
    cases vs with
    | nil => simp [compileRoutedBank] at h
    | cons vlow vmid =>
      simp only [compileRoutedBank] at h
      split at h
      next valid => cases h; exact ⟨valid,rfl,rfl,rfl,rfl,rfl,rfl⟩
      next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
