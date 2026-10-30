import ECDSAAdd.Submission.Entrant.DiagSquare



-- ONEFLAG COMPONENT OneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagCell
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
attribute [local irreducible] run wires

def selectSwap (w : Nat → Wire) (b sw flag : Wire) (constant : Bool) : Program :=
  transcriptSelectWindow b sw flag constant
    (swapRegisters flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)

def halfWindow (divide : Bool) (w : Nat → Wire) (b g flag : Wire) (constant : Bool) : Program :=
  transcriptSelectWindow b g flag constant (Q6EndpointCell.half divide w flag)

def cell (divide : Bool) (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool) : Program :=
  if divide then halfWindow true w b g flag ig ++ selectSwap w b sw flag is
  else selectSwap w b sw flag is ++ halfWindow false w b g flag ig

theorem swap_frame (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (origin : BasisState) (A B : Nat) :
    Triple (PairFrame r y origin A B) (swapRegisters c r y)
      (PairFrame r y origin (if origin c then B else A) (if origin c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem selectSwap_frame (w : Nat → Wire) (b sw flag : Wire) (constant : Bool)
    (ns : (flag::(Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y).Nodup)
    (nd : [b,sw,flag].Nodup)
    (hb : b∉(Q6EndpointCell.ports w flag).r ∧ b∉(Q6EndpointCell.ports w flag).y)
    (hsw : sw∉(Q6EndpointCell.ports w flag).r ∧ sw∉(Q6EndpointCell.ports w flag).y)
    (hf : flag∉(Q6EndpointCell.ports w flag).r ∧ flag∉(Q6EndpointCell.ports w flag).y)
    (origin : BasisState) (hz : origin flag=false) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
      (centerWord X) (centerWord Y)) (selectSwap w b sw flag constant)
      (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
        (centerWord (if mixedTranscriptBit origin b sw constant then Y else X))
        (centerWord (if mixedTranscriptBit origin b sw constant then X else Y))) := by
  let L := Q6EndpointCell.ports w flag
  have len := BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths w flag)
  have h := swap_frame L.r L.y flag (len.2.1.trans len.2.2.1.symm) ns
    (mixedTranscriptBase origin b sw flag constant) (centerWord X) (centerWord Y)
  have flagval : mixedTranscriptBase origin b sw flag constant flag =
      mixedTranscriptBit origin b sw constant := by simp [mixedTranscriptBase,writeBit]
  rw [flagval] at h
  have h' := transcriptSelectWindow_pairFrame b sw flag constant L.r L.y nd hb hsw hf
    origin hz (centerWord X) (centerWord Y)
    (if mixedTranscriptBit origin b sw constant then centerWord Y else centerWord X)
    (if mixedTranscriptBit origin b sw constant then centerWord X else centerWord Y) _ h
  cases e : mixedTranscriptBit origin b sw constant <;>
    simpa only [selectSwap,e,Bool.false_eq_true,if_true,if_false] using h'

theorem halfWindow_frame (divide : Bool) (w : Nat → Wire) (b g flag : Wire) (constant : Bool)
    (hn : (Q6EndpointCell.ports w flag).wires.Nodup) (nd : [b,g,flag].Nodup)
    (hb : b∉(Q6EndpointCell.ports w flag).r ∧ b∉(Q6EndpointCell.ports w flag).y)
    (hg : g∉(Q6EndpointCell.ports w flag).r ∧ g∉(Q6EndpointCell.ports w flag).y)
    (hf : flag∉(Q6EndpointCell.ports w flag).r ∧ flag∉(Q6EndpointCell.ports w flag).y)
    (hfw : flag∉Q6EndpointCell.workIds.map w)
    (origin : BasisState) (hz : origin flag=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
      (centerWord X) (centerWord Y)) (halfWindow divide w b g flag constant)
      (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
        (centerWord (if divide then (X+(if mixedTranscriptBit origin b g constant then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit origin b g constant then -Y else Y))) (centerWord Y)) := by
  have cl : Q6EndpointCell.Clean w (mixedTranscriptBase origin b g flag constant) := by
    intro q hq
    have ne:q≠flag:=fun e=>hfw (e ▸ hq)
    simpa only [mixedTranscriptBase,writeBit,Function.update_of_ne ne] using hc q hq
  have body := Q6EndpointCell.half_frame divide w flag hn (mixedTranscriptBase origin b g flag constant) cl X Y
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  exact transcriptSelectWindow_pairFrame b g flag constant _ _ nd hb hg hf origin hz _ _ _ _ _ body

theorem cell_frame (divide : Bool) (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool)
    (hn : (Q6EndpointCell.ports w flag).wires.Nodup)
    (ns : (flag::(Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y).Nodup)
    (ng : [b,g,flag].Nodup) (nS : [b,sw,flag].Nodup)
    (hb : b∉(Q6EndpointCell.ports w flag).r ∧ b∉(Q6EndpointCell.ports w flag).y)
    (hg : g∉(Q6EndpointCell.ports w flag).r ∧ g∉(Q6EndpointCell.ports w flag).y)
    (hs : sw∉(Q6EndpointCell.ports w flag).r ∧ sw∉(Q6EndpointCell.ports w flag).y)
    (hf : flag∉(Q6EndpointCell.ports w flag).r ∧ flag∉(Q6EndpointCell.ports w flag).y)
    (hfw : flag∉Q6EndpointCell.workIds.map w)
    (origin : BasisState) (hz : origin flag=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
      (centerWord X) (centerWord Y)) (cell divide w b g sw flag ig is)
      (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
        (centerWord (Q6EndpointCell.payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).1)
        (centerWord (Q6EndpointCell.payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).2)) := by
  cases divide
  · let A := if mixedTranscriptBit origin b sw is then Y else X
    let B := if mixedTranscriptBit origin b sw is then X else Y
    have a := selectSwap_frame w b sw flag is ns nS hb hs hf origin hz X Y
    have z := halfWindow_frame false w b g flag ig hn ng hb hg hf hfw origin hz hc A B
    cases es : mixedTranscriptBit origin b sw is <;>
      simpa only [cell,Bool.false_eq_true,if_false,if_true,Q6EndpointCell.payload,skywalkPayloadUncell,A,B,es,
        Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] using a.seq z
  · let T := (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2
    have a := halfWindow_frame true w b g flag ig hn ng hb hg hf hfw origin hz hc X Y
    have z := selectSwap_frame w b sw flag is ns nS hb hs hf origin hz T Y
    cases es : mixedTranscriptBit origin b sw is <;>
      simpa only [cell,Bool.false_eq_true,if_true,if_false,Q6EndpointCell.payload,skywalkPayloadCell,T,es,
        Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] using a.seq z

theorem counts (divide : Bool) (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool)
    (ns : (flag::(Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y).Nodup) :
    toffoliCount (cell divide w b g sw flag ig is)=1278 ∧
      measurementCount (cell divide w b g sw flag ig is)=1023 := by
  have len := BalancedCleanup.widths (Q6EndpointCell.ports w flag).toLayout (Q6EndpointCell.ports_widths w flag)
  have s := swapRegisters_resources flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y
    (len.2.1.trans len.2.2.1.symm) ns
  have h := transcriptSelectWindow_counts b sw flag is
    (swapRegisters flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)
  have k := Q6EndpointCell.half_counts divide w flag
  have e := transcriptSelectWindow_counts b g flag ig (Q6EndpointCell.half divide w flag)
  cases divide <;> simp only [cell,selectSwap,halfWindow,Bool.false_eq_true,if_true,if_false,
    toffoliCount_append,measurementCount_append] <;>
    rw [h.1,h.2,s.1,s.2.1,len.2.1,e.1,e.2,k.1,k.2] <;> omega

theorem select_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆[b,source,flag].toFinset∪wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

theorem selectSwap_support (w : Nat → Wire) (b sw flag : Wire) (constant : Bool)
    (W : Finset Wire) (hi : (flag::Q6EndpointCell.ids.map w).toFinset⊆W)
    (hb : b∈W) (hs : sw∈W) : wires (selectSwap w b sw flag constant)⊆W := by
  have hf : flag∈W := hi (by simp)
  have len := BalancedCleanup.widths (Q6EndpointCell.ports w flag).toLayout (Q6EndpointCell.ports_widths w flag)
  have swp := swapRegisters_wires flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y
    (len.2.1.trans len.2.2.1.symm)
  have ports := Q6EndpointCell.ports_wires_sub w flag W hi
  have rs : (flag::((Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y)).toFinset⊆W := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with h|h|h
    · exact h ▸ hf
    · exact ports (List.mem_toFinset.mpr (by
        simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢
        tauto))
    · exact ports (List.mem_toFinset.mpr (by
        simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢
        tauto))
  exact (select_support b sw flag constant _).trans (Finset.union_subset
    (by simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_subset_iff,Finset.empty_subset,and_true] using And.intro hb (And.intro hs hf)) (swp.trans rs))

theorem support (divide : Bool) (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool)
    (W : Finset Wire) (hi : (flag::Q6EndpointCell.ids.map w).toFinset⊆W)
    (hb : b∈W) (hg : g∈W) (hs : sw∈W) : wires (cell divide w b g sw flag ig is)⊆W := by
  have hf : flag∈W := hi (by simp)
  have e : wires (halfWindow divide w b g flag ig)⊆W :=
    (select_support b g flag ig _).trans (Finset.union_subset
      (by simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_subset_iff,Finset.empty_subset,and_true] using And.intro hb (And.intro hg hf))
      (Q6EndpointCell.half_support divide w flag W hi))
  have z := selectSwap_support w b sw flag is W hi hb hs
  cases divide <;> simp only [cell,Bool.false_eq_true,if_false,if_true,wires_append] <;>
    first | exact Finset.union_subset (by simpa using z) (by simpa using e)
          | exact Finset.union_subset (by simpa using e) (by simpa using z)

theorem cell_frame_legacy (divide : Bool) (w : Nat → Wire) (b g sw sign eff : Wire)
    (ig is : Bool) (hl : BalancedTranscriptLayout (Q6EndpointCell.ports w sign) b g sw eff)
    (origin : BasisState) (hz : origin sign=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y)) (cell divide w b g sw sign ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (Q6EndpointCell.payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).1)
        (centerWord (Q6EndpointCell.payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).2)) := by
  have ng : [b,g,sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [Q6EndpointCell.ports_sign,List.count_cons,List.count_nil] at h ⊢
    omega
  have ns : [b,sw,sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [Q6EndpointCell.ports_sign,List.count_cons,List.count_nil] at h ⊢
    omega
  have nd : (sign::(Q6EndpointCell.ports w sign).r++(Q6EndpointCell.ports w sign).y).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.kernel q
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil,
      Q6EndpointCell.ports_sign] at h ⊢
    omega
  have fw : sign∉Q6EndpointCell.workIds.map w := by
    have a := OneBankCore5.sign_work (Q6EndpointCell.ports w sign) hl.kernel
    simpa only [Q6EndpointCell.ports_sign,Q6EndpointCell.ports_work] using a
  exact cell_frame divide w b g sw sign ig is hl.kernel nd ng ns
    (hl.outside b (by simp)) (hl.outside g (by simp)) (hl.outside sw (by simp))
    (hl.outside sign (by simp [Q6EndpointCell.ports_sign])) fw origin hz hc X Y

section Physical
open Challenge Baselines

theorem physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w)
    (b g sw : Wire) (ig is : Bool)
    (ng : [b,g,w 2409].Nodup) (ns : [b,sw,w 2409].Nodup)
    (nd : (w 2409::(Q6EndpointCell.ports w (w 2409)).r++(Q6EndpointCell.ports w (w 2409)).y).Nodup) :
    GatePhysical (cell divide w b g sw (w 2409) ig is) := by
  have h := Q6EndpointCell.half_physical divide w hw
  have swp := swapRegisters_physical (w 2409) _ _ nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at ng ns
  have a := transcriptWindow_physical b g (w 2409) ig _ (by tauto) (by tauto) h
  have z := transcriptWindow_physical b sw (w 2409) is _ (by tauto) (by tauto) swp
  cases divide <;> simp only [cell,halfWindow,selectSwap,Bool.false_eq_true,if_true,if_false,gatePhysical_append] <;>
    first | exact ⟨a,z⟩ | exact ⟨z,a⟩

theorem gateSlots_le (divide : Bool) (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool) :
    gateSlots (cell divide w b g sw flag ig is)≤26000 := by
  have h := Q6EndpointCell.half_gateSlots_le divide w flag
  have len := BalancedCleanup.widths (Q6EndpointCell.ports w flag).toLayout (Q6EndpointCell.ports_widths w flag)
  have swap : gateSlots (swapRegisters flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)≤768 := by
    rw [swapRegisters_gateSlots,len.2.1]
    omega
  have a := selectWindow_gateSlots_le b g flag ig (Q6EndpointCell.half divide w flag)
  have z := selectWindow_gateSlots_le b sw flag is
    (swapRegisters flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)
  cases divide <;> simp only [cell,halfWindow,selectSwap,Bool.false_eq_true,if_true,if_false,gateSlots_append] <;> omega
end Physical

attribute [local irreducible] cell Q6EndpointCell.ids

theorem retired_free (divide : Bool) (w : Nat → Wire) (b g sw flag q : Wire) (ig is : Bool)
    (hf : q≠flag) (hb : q≠b) (hg : q≠g) (hs : q≠sw)
    (hi : q∉Q6EndpointCell.ids.map w) : q∉wires (cell divide w b g sw flag ig is) := by
  let W := (flag::b::g::sw::Q6EndpointCell.ids.map w).toFinset
  have sub : (flag::Q6EndpointCell.ids.map w).toFinset⊆W := by
    intro x hx
    simp only [W,List.mem_toFinset,List.mem_cons] at hx ⊢
    tauto
  have away : q∉W := by simp [W,hf,hb,hg,hs,hi]
  exact fun h=>away (support divide w b g sw flag ig is W sub (by simp [W]) (by simp [W]) (by simp [W]) h)

theorem eff2410_free (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : g≠base 2410) (hs : sw≠base 2410) :
    base 2410∉wires (cell divide base (base 2400) g sw (base 2409) ig is) := by
  apply retired_free divide base (base 2400) g sw (base 2409) (base 2410) ig is
  · intro e; have := base_injective e; omega
  · intro e; have := base_injective e; omega
  · exact Ne.symm hg
  · exact Ne.symm hs
  · intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have bound := Q6EndpointCell.ids_bound i hi
    have := base_injective he
    omega
end ECDSAAdd.Entrant.OneFlagCell


-- ONEFLAG COMPONENT TerminalSwap.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagCell
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport
attribute [local irreducible] run wires

def selectMSwap (w : Nat → Wire) (b sw flag : Wire) (constant : Bool) : Program :=
  transcriptSelectWindow b sw flag constant
    (UncompSwap.mswap flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)

theorem selectMSwap_frame (w : Nat → Wire) (b sw flag : Wire) (constant : Bool)
    (ns : (flag::(Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y).Nodup)
    (nd : [b,sw,flag].Nodup)
    (hb : b∉(Q6EndpointCell.ports w flag).r ∧ b∉(Q6EndpointCell.ports w flag).y)
    (hsw : sw∉(Q6EndpointCell.ports w flag).r ∧ sw∉(Q6EndpointCell.ports w flag).y)
    (hf : flag∉(Q6EndpointCell.ports w flag).r ∧ flag∉(Q6EndpointCell.ports w flag).y)
    (origin : BasisState) (hz : origin flag=false) (X Y : Fp)
    (hzero : (if mixedTranscriptBit origin b sw constant then X else Y)=0) :
    Triple (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
      (centerWord X) (centerWord Y)) (selectMSwap w b sw flag constant)
      (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
        (centerWord (if mixedTranscriptBit origin b sw constant then Y else X))
        (centerWord (if mixedTranscriptBit origin b sw constant then X else Y))) := by
  let L := Q6EndpointCell.ports w flag
  have len := BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths w flag)
  have flagval : mixedTranscriptBase origin b sw flag constant flag =
      mixedTranscriptBit origin b sw constant := by simp [mixedTranscriptBase,writeBit]
  have zero : (if mixedTranscriptBase origin b sw flag constant flag then centerWord X else centerWord Y)=0 := by
    rw [flagval]
    cases bit : mixedTranscriptBit origin b sw constant <;>
      simp only [bit,if_true,if_false,Bool.false_eq_true] at hzero ⊢ <;> rw [hzero,UncompSwap.centerWord_zero]
  have h := UncompSwap.mswap_pair L.r L.y flag (len.2.1.trans len.2.2.1.symm) ns
    (mixedTranscriptBase origin b sw flag constant) (centerWord X) (centerWord Y) zero
  rw [flagval] at h
  have h' := transcriptSelectWindow_pairFrame b sw flag constant L.r L.y nd hb hsw hf
    origin hz (centerWord X) (centerWord Y)
    (if mixedTranscriptBit origin b sw constant then centerWord Y else centerWord X)
    (if mixedTranscriptBit origin b sw constant then centerWord X else centerWord Y) _ h
  cases e : mixedTranscriptBit origin b sw constant <;>
    simpa only [selectMSwap,e,Bool.false_eq_true,if_true,if_false] using h'

def terminalCell (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool) : Program :=
  selectMSwap w b sw flag is ++ halfWindow false w b g flag ig

theorem terminalCell_frame (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool)
    (hn : (Q6EndpointCell.ports w flag).wires.Nodup)
    (ns : (flag::(Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y).Nodup)
    (ng : [b,g,flag].Nodup) (nS : [b,sw,flag].Nodup)
    (hb : b∉(Q6EndpointCell.ports w flag).r ∧ b∉(Q6EndpointCell.ports w flag).y)
    (hg : g∉(Q6EndpointCell.ports w flag).r ∧ g∉(Q6EndpointCell.ports w flag).y)
    (hs : sw∉(Q6EndpointCell.ports w flag).r ∧ sw∉(Q6EndpointCell.ports w flag).y)
    (hf : flag∉(Q6EndpointCell.ports w flag).r ∧ flag∉(Q6EndpointCell.ports w flag).y)
    (hfw : flag∉Q6EndpointCell.workIds.map w)
    (origin : BasisState) (hz : origin flag=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (hzero : (if mixedTranscriptBit origin b sw is then X else Y)=0) :
    Triple (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
      (centerWord X) (centerWord Y)) (terminalCell w b g sw flag ig is)
      (PairFrame (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y origin
        (centerWord (Q6EndpointCell.payload false (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).1)
        (centerWord (Q6EndpointCell.payload false (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).2)) := by
  let A := if mixedTranscriptBit origin b sw is then Y else X
  let B := if mixedTranscriptBit origin b sw is then X else Y
  have a := selectMSwap_frame w b sw flag is ns nS hb hs hf origin hz X Y hzero
  have z := halfWindow_frame false w b g flag ig hn ng hb hg hf hfw origin hz hc A B
  cases es : mixedTranscriptBit origin b sw is <;>
    simpa only [terminalCell,Bool.false_eq_true,if_false,if_true,Q6EndpointCell.payload,skywalkPayloadUncell,A,B,es,
      Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] using a.seq z

theorem terminal_counts (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool) :
    toffoliCount (terminalCell w b g sw flag ig is)=1022 ∧
      measurementCount (terminalCell w b g sw flag ig is)=1279 := by
  have len := BalancedCleanup.widths (Q6EndpointCell.ports w flag).toLayout (Q6EndpointCell.ports_widths w flag)
  have s := UncompSwap.mswap_counts flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y
    (len.2.1.trans len.2.2.1.symm)
  have h := transcriptSelectWindow_counts b sw flag is
    (UncompSwap.mswap flag (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)
  have k := Q6EndpointCell.half_counts false w flag
  have e := transcriptSelectWindow_counts b g flag ig (Q6EndpointCell.half false w flag)
  simp only [terminalCell,selectMSwap,halfWindow,toffoliCount_append,measurementCount_append]
  rw [h.1,h.2,s.1,s.2,len.2.1,e.1,e.2,k.1,k.2]
  omega

theorem selectMSwap_wires (w : Nat → Wire) (b sw flag : Wire) (constant : Bool) :
    wires (selectMSwap w b sw flag constant)=wires (selectSwap w b sw flag constant) := by
  simp only [selectMSwap,selectSwap,transcriptSelectWindow,wires_append,UncompSwap.mswap_wires]

theorem terminal_wires (w : Nat → Wire) (b g sw flag : Wire) (ig is : Bool) :
    wires (terminalCell w b g sw flag ig is)=wires (cell false w b g sw flag ig is) := by
  simp only [terminalCell,cell,Bool.false_eq_true,if_false,wires_append,selectMSwap_wires]

theorem terminal_eff2410_free (g sw : Wire) (ig is : Bool)
    (hg : g≠base 2410) (hs : sw≠base 2410) :
    base 2410∉wires (terminalCell base (base 2400) g sw (base 2409) ig is) := by
  rw [terminal_wires]
  exact eff2410_free false g sw ig is hg hs
end ECDSAAdd.Entrant.OneFlagCell


-- ONEFLAG COMPONENT Replay.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

structure Context (origin : BasisState) : Prop where
  hn : (skywalkSharedWires base).Nodup
  ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base
  hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base
  hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)
  hg0 : origin (base 2409)=false
  hs0 : origin (base 2410)=false
  env : Env base origin
  legal : History5.RawLegal base 102 origin
  parity : origin (base 2312)=false

def rawReplay (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then
      OneFlagCell.cell true base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2++rawReplay true ls
    else rawReplay false ls++
      OneFlagCell.cell false base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2

def body (divide : Bool) (j : Nat) : Program := rawReplay divide (Replay5.letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++body divide j++History5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstSwap : Program := OneFlagCell.selectSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2
def firstSwapM : Program := OneFlagCell.selectMSwap base (base 2400) (base 1028) (base 2409)
  (mixedTranscriptUnitTrace.getD 0 (false,false)).2

def firstBody (divide : Bool) : Program :=
  if divide then firstSwap++rawReplay true Replay5.restLetters
  else rawReplay false Replay5.restLetters++firstSwapM

def baseFirstPacket (divide : Bool) : Program :=
  History5.decode base 0++firstBody divide++History5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  Q6EndpointCell.endpoint divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def logicalReplay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplay divide)


def fieldSites : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset

def readSites (start : Nat) : Finset Wire := fieldSites ∪ {base 2400,base 2410} ∪
  wires (History5.encode base start)

theorem raw_support (divide : Bool) (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (hi : fieldSites⊆W) (hb : base 2400∈W) (he : base 2410∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) : wires (rawReplay divide ls)⊆W := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := OneFlagCell.support divide base (base 2400) l.1.1 l.1.2 (base 2409)
      l.2.1 l.2.2 W hi hb (controls l (by simp)).1 (controls l (by simp)).2
    have rest := ih (fun k hk => controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.union_subset_iff] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆readSites (5*j) := by
  apply raw_support
  · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · intro l hl
    have c := Replay5.letters_controls j hj l hl
    exact ⟨Finset.mem_union_right _ c.1,Finset.mem_union_right _ c.2⟩

theorem readSites_sub (start : Nat) : readSites start⊆
    History5.groupReadSites base (base 2400) (base 2409) (base 2410) start ∪ {base 2312} := by
  intro q hq
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem body_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (body_support divide j hj).trans (readSites_sub (5*j))

theorem firstBody_support (divide : Bool) : wires (firstBody divide)⊆readSites 0 := by
  let W := readSites 0
  have hi : fieldSites⊆W := fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hb : base 2400∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have he : base 2410∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have hs : base 1028∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 0 (by decide)).2)
  have swap : wires firstSwap⊆W := OneFlagCell.selectSwap_support base (base 2400) (base 1028)
    (base 2409) _ W hi hb hs
  have rest : wires (rawReplay divide Replay5.restLetters)⊆W := by
    apply raw_support divide Replay5.restLetters W hi hb he
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    have controls := Replay5.history_controls 0 k (by omega)
    simp only [Nat.zero_add] at controls
    simpa only [tapeLetter,tape] using
      (show base k∈W ∧ base (1028+k)∈W from
        ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩)
  have swapM : wires firstSwapM⊆W := by
    change wires (OneFlagCell.selectMSwap _ _ _ _ _)⊆W
    rw [OneFlagCell.selectMSwap_wires]; exact swap
  cases divide <;> simp only [firstBody,Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff]
  · exact ⟨rest,swapM⟩
  · exact ⟨swap,rest⟩

theorem firstBody_read_support (divide : Bool) :
    wires (firstBody divide)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  (firstBody_support divide).trans (readSites_sub 0)

theorem rawEnd_support (divide : Bool) : wires (rawEnd divide)⊆fieldSites ∪ {base 2400,base 510} := by
  apply Q6EndpointCell.endpoint_support divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  · exact Finset.subset_union_left
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)

theorem rawEnd_read_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2312,base 2400,base 510} := by
  intro q hq
  rcases Finset.mem_union.mp (rawEnd_support divide hq) with h|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ (by simp [h])
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Finset.mem_union_right _ (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (History5.allEncode base 102)) (wires (rawEnd divide)) := by
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member base 102 q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q member
  have read := rawEnd_read_support divide used
  rcases Finset.mem_union.mp read with read|read
  · exact History5.history_active_away base (base 2409) hn (hp _ (by simp)) (5*j) (by omega) r
      (List.mem_toFinset.mp read)
  · have bound := History5.historyId_bound (5*j) (by omega) r
    have own : History5.historyMap base (5*j) r∈skywalkPoolWires base := by
      exact List.mem_map.mpr ⟨History5.historyId (5*j) r,by simp only [List.mem_range'_1]; omega,rfl⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at read
    rcases read with eq|eq|eq
    · have same := base_injective eq
      omega
    · exact hp _ (by simp) (eq ▸ own)
    · have same := base_injective eq
      have rr := r.isLt
      unfold History5.historyId at same
      split_ifs at same <;> omega

private theorem q7part2_letter_layout (origin : BasisState) (ctx : Context origin)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (l : MixedTranscriptLetter) (hl : l∈ls) :
    BalancedTranscriptLayout (Q6EndpointCell.ports base (base 2409))
      (base 2400) l.1.1 l.1.2 (base 2410) :=
  Q6EndpointCell.ports_transcript base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) (hf l hl) ctx.ho)
    (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

theorem raw_frame (divide : Bool) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawReplay divide ls)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).2)) := by
  have clean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  induction ls generalizing X Y with
  | nil =>
    intro s m h
    cases divide <;> simpa only [rawReplay,directionalPayload,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,mixedTranscriptControls,List.map_nil,skywalkPayloadReplay,
      skywalkPayloadReplayInverse,run] using And.intro (Eq.refl s.phase) h
  | cons l ls ih =>
    have layout := q7part2_letter_layout origin ctx (l::ls) hf l (by simp)
    have tailLayout := fun k hk => hf k (List.mem_cons_of_mem l hk)
    cases divide
    · let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) ls) (X,Y)
      have rest := ih tailLayout X Y
      have head := OneFlagCell.cell_frame_legacy false base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean Q.1 Q.2
      simpa only [rawReplay,Bool.false_eq_true,if_false,directionalPayload,Bool.not_false,if_true,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using rest.seq head
    · let Q := skywalkPayloadCell (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1)
        (mixedTranscriptBit origin (base 2400) l.1.2 l.2.2) (X,Y)
      have head := OneFlagCell.cell_frame_legacy true base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 clean X Y
      have rest := ih tailLayout Q.1 Q.2
      simpa only [rawReplay,if_true,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using head.seq rest

private theorem q7part2_rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem q7part2_first_layout (origin : BasisState) (ctx : Context origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have h := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at h
  exact h

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have raw := raw_frame divide (Replay5.letters j) (Replay5.letters_layouts ctx.hf j hj) origin ctx X Y
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp j hj origin X Y _ _ _ (body_read_support divide j hj) raw s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.groupsPayload divide origin j n (X,Y)).1
        (Replay5.groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun V t => History5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk origin ctx V.1 V.2 t records h⟩)
    j n bound (X,Y) s m input
  exact result.2


theorem base_sign_nd : (base 2409::(Q6EndpointCell.ports base (base 2409)).r++
    (Q6EndpointCell.ports base (base 2409)).y).Nodup := by
  have away : base 2409∉Q6EndpointCell.ids.map base := by
    intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have bound := Q6EndpointCell.ids_bound i hi
    have := base_injective he
    omega
  have hn := Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective away
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil,
    Q6EndpointCell.ports_sign] at h ⊢
  omega

theorem firstBody_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.firstPayload divide origin (X,Y)).1)
        (centerWord (Replay5.firstPayload divide origin (X,Y)).2)) := by
  let S := mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  have nl := Q6EndpointCell.ports_transcript base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) ctx.hn (q7part2_first_layout origin ctx) (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have hb := nl.outside (base 2400) (by simp)
  have hs := nl.outside (base 1028) (by simp)
  have hf := nl.outside (base 2409) (by simp [Q6EndpointCell.ports_sign])
  have swap := OneFlagCell.selectSwap_frame base (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0
  cases divide
  · let V := directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X,Y)
    have zero : (if S then V.1 else V.2)=0 := by
      have h := hz rfl
      have k : ∀ (b : Bool) (p : Fp×Fp), (if b then (p.2,p.1) else p).2=(if b then p.1 else p.2) := by
        intro b p; cases b <;> rfl
      simp only [Replay5.firstPayload,Bool.false_eq_true,if_false,k] at h
      exact h
    have swapM := OneFlagCell.selectMSwap_frame base (base 2400) (base 1028) (base 2409)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2 base_sign_nd (by decide) hb hs hf origin ctx.hg0 V.1 V.2 zero
    have rest := raw_frame false Replay5.restLetters (q7part2_rest_layout ctx.hf) origin ctx X Y
    have out := rest.seq swapM
    cases hS : S <;> simpa only [firstBody,firstSwapM,Replay5.firstPayload,Bool.false_eq_true,
      if_false,Bool.not_false,if_true,S,hS,V] using out
  · have out := (swap X Y).seq (raw_frame true Replay5.restLetters (q7part2_rest_layout ctx.hf)
      origin ctx (if S then Y else X) (if S then X else Y))
    cases hS : S <;> simpa only [firstBody,firstSwap,Replay5.firstPayload,if_true,Bool.not_true,
      Bool.false_eq_true,if_false,S,hS] using out

theorem firstPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.firstPayload divide origin (X,Y)).1
        (Replay5.firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin X Y _ _ _ (firstBody_read_support divide)
    (firstBody_frame divide origin ctx X Y hz) s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) (baseFirstPacket divide)
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  first
  | exact Q6EndpointReplay.rawEnd_frame divide origin oldctx X Y hend
  | exact Q6EndpointReplay.rawEnd_frame divide origin oldctx X Y

theorem endPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  first
  | exact Q6EndpointReplay.endPacket_frame divide origin oldctx X Y hend s m input
  | exact Q6EndpointReplay.endPacket_frame divide origin oldctx X Y s m input

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false origin ctx Y Y (fun e => absurd e (by decide)) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  FieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  FieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame origin ctx x hx0 hx trace Y) s m input


















end ECDSAAdd.Entrant.OneFlagReplay


-- ONEFLAG COMPONENT Omissions.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic MappedCompressed
attribute [local irreducible] wires rawReplay OneFlagCell.cell Q6EndpointCell.ids

theorem codec_eff_free (start : Nat) (hs : start+5≤512) (p : Program)
    (hp : p=History5.encode base start ∨ p=History5.decode base start) : base 2410∉wires p := by
  intro h
  obtain ⟨i,hi⟩ := History5.history_gate_mem base start p hp (base 2410) h
  have bound := History5.historyId_bound start hs i
  have e := base_injective hi
  change 2410=History5.historyId start i at e
  omega

theorem raw_eff_free (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,l.1.1≠base 2410 ∧ l.1.2≠base 2410) :
    base 2410∉wires (rawReplay divide ls) := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := OneFlagCell.eff2410_free divide l.1.1 l.1.2 l.2.1 l.2.2
      (controls l (by simp)).1 (controls l (by simp)).2
    have rest := ih (fun k hk=>controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_eff_free (divide : Bool) (j : Nat) (hj : j<102) : base 2410∉wires (body divide j) := by
  apply raw_eff_free
  intro l hl
  have c := Replay5.letters_controls j hj l hl
  have avoid := codec_eff_free (5*j) (by omega) (History5.encode base (5*j)) (Or.inl rfl)
  exact ⟨fun e=>avoid (e ▸ c.1),fun e=>avoid (e ▸ c.2)⟩

theorem basePacket_eff_free (divide : Bool) (j : Nat) (hj : j<102) :
    base 2410∉wires (basePacket divide j) := by
  have e := codec_eff_free (5*j) (by omega) (History5.encode base (5*j)) (Or.inl rfl)
  have d := codec_eff_free (5*j) (by omega) (History5.decode base (5*j)) (Or.inr rfl)
  have b := body_eff_free divide j hj
  simpa only [basePacket,wires_append,Finset.mem_union,not_or] using And.intro (And.intro d b) e

theorem rename_free (f : Wire→Wire) (inj : Function.Injective f) (q q' : Wire) (fix : f q'=q)
    (P : Program) (away : q'∉wires P) : q∉wires (renameProgram f P) := by
  rw [renameProgram_support]
  intro h
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp h
  have e:r=q' := inj (he.trans fix.symm)
  exact away (e ▸ hr)

theorem packet_eff_free (divide : Bool) (j : Nat) (hj : j<102) : base 2410∉wires (packet divide j) := by
  exact rename_free (shifted (Placement5.pi j)) (shifted (Placement5.pi j)).injective _ _
    (by rw [shifted_base,Placement5.pi_outside j 2410 hj (by simp [Placement5.zeroRegion,Placement5.workRegion,Placement5.holeRegion])]) _ (basePacket_eff_free divide j hj)

theorem groups_eff_free (divide : Bool) (j n : Nat) (h : j+n≤102) :
    base 2410∉wires (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,wires]
  | succ n ih =>
    have head := packet_eff_free divide j (by omega)
    have tail := ih (j+1) (by omega)
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem firstSwap_eff_free : base 2410∉wires firstSwap := by
  have c := OneFlagCell.eff2410_free true (base 0) (base 1028) false
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 (by decide) (by decide)
  intro h
  apply c
  rw [OneFlagCell.cell,if_pos rfl]
  change base 2410∈wires (OneFlagCell.halfWindow true base (base 2400) (base 0) (base 2409) false ++ firstSwap)
  rw [wires_append]
  exact Finset.mem_union_right _ h

theorem firstSwapM_eff_free : base 2410∉wires firstSwapM := by
  change base 2410∉wires (OneFlagCell.selectMSwap _ _ _ _ _)
  rw [OneFlagCell.selectMSwap_wires]
  exact firstSwap_eff_free

theorem firstBody_eff_free (divide : Bool) : base 2410∉wires (firstBody divide) := by
  have rest : base 2410∉wires (rawReplay divide Replay5.restLetters) := by
    apply raw_eff_free
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    simp only [tapeLetter,tape,Prod.fst,Prod.snd]
    constructor <;> intro e <;> have := base_injective e <;> omega
  cases divide <;> simp only [firstBody,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.mem_union,not_or] at rest ⊢
  · exact ⟨rest,firstSwapM_eff_free⟩
  · exact ⟨firstSwap_eff_free,rest⟩

theorem firstPacket_eff_free (divide : Bool) : base 2410∉wires (firstPacket divide) := by
  have e := codec_eff_free 0 (by decide) (History5.encode base 0) (Or.inl rfl)
  have d := codec_eff_free 0 (by decide) (History5.decode base 0) (Or.inr rfl)
  have b := firstBody_eff_free divide
  have away : base 2410∉wires (baseFirstPacket divide) := by
    simpa only [baseFirstPacket,wires_append,Finset.mem_union,not_or] using And.intro (And.intro d b) e
  exact rename_free (shifted (Placement5.pi 0)) (shifted (Placement5.pi 0)).injective _ _
    (by rw [shifted_base,Placement5.pi_outside 0 2410 (by decide) (by simp [Placement5.zeroRegion,Placement5.workRegion,Placement5.holeRegion])]) _ away

theorem fieldSites_eff_free : base 2410∉fieldSites := by
  intro h
  change base 2410∈(base 2409::Q6EndpointCell.ids.map base).toFinset at h
  simp only [List.mem_toFinset,List.mem_cons] at h
  rcases h with h|h
  · have := base_injective h; omega
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have bound := Q6EndpointCell.ids_bound i hi
    have := base_injective he
    omega

theorem endPacket_eff_free (divide : Bool) : base 2410∉wires (endPacket divide) := by
  have away : base 2410∉wires (rawEnd divide) := by
    intro h
    have sub := rawEnd_support divide h
    rcases Finset.mem_union.mp sub with h|h
    · exact fieldSites_eff_free h
    · have n : base 2410∉({base 2400,base 510}:Finset Wire) := by decide
      exact n h
  exact rename_free (shifted Placement5.pi0) (shifted Placement5.pi0).injective _ _
    (by rw [shifted_base,Placement5.pi0_outside 2410 (by simp [Placement5.zeroRegion,Placement5.workRegion,Placement5.holeRegion])]) _ away

theorem replay_eff_free (divide : Bool) : base 2410∉wires (replay divide) := by
  have a := firstPacket_eff_free divide
  have b := groups_eff_free divide 1 101 (by decide)
  have c := endPacket_eff_free divide
  have away : base 2410∉wires (logicalReplay divide) := by
    cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.mem_union,not_or] at a b c ⊢
    · exact ⟨⟨c,b⟩,a⟩
    · exact ⟨⟨a,b⟩,c⟩
  exact rename_free (OB5.sig 511) (OB5.sig_injective 511 (by decide)) _ _ (by decide) _ away

/-- Existing host permutation can be retained: absent input2410 maps to absent output1542. -/
theorem hosted_replay_1542_free (divide : Bool) :
    base 1542∉wires (renameProgram HostOB5.hostSwap (replay divide)) :=
  rename_free HostOB5.hostSwap HostOB5.hostSwap_injective _ _ (by decide) _ (replay_eff_free divide)
end ECDSAAdd.Entrant.OneFlagReplay


-- ONEFLAG COMPONENT Resources.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount
section Counts

private theorem q7part4_swap_nodup (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    (base 2410::(Q6EndpointCell.ports base (base 2409)).r++(Q6EndpointCell.ports base (base 2409)).y).Nodup := by
  have own : base 2410∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2410) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2410)) nd (base 2410)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2410) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2410∈(balancedSharedPorts base (base 2410)).r := by
      simpa only [Q6EndpointCell.ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2410∈(balancedSharedPorts base (base 2410)).y := by
      simpa only [Q6EndpointCell.ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

theorem raw_counts (divide : Bool) (ls : List MixedTranscriptLetter)
    (hs : (base 2410::(Q6EndpointCell.ports base (base 2409)).r++(Q6EndpointCell.ports base (base 2409)).y).Nodup) :
    toffoliCount (rawReplay divide ls)=ls.length*1278 ∧
      measurementCount (rawReplay divide ls)=ls.length*1023 := by
  induction ls with
  | nil => simp [rawReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have c := OneFlagCell.counts divide base (base 2400) l.1.1 l.1.2 (base 2409)
      l.2.1 l.2.2 base_sign_nd
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,List.length_cons] at c ih ⊢
    all_goals constructor <;> omega

theorem packet_counts (divide : Bool) (j : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (packet divide j)=6410 ∧ measurementCount (packet divide j)=5121 := by
  have raw := raw_counts divide (Replay5.letters j) (q7part4_swap_nodup hn ho)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at raw
  have e := History5.encode_counts base (5*j)
  have d := History5.decode_counts base (5*j)
  have renamed := renameProgram_counts (shifted (Placement5.pi j)) (basePacket divide j)
  change toffoliCount (renameProgram _ (basePacket divide j))=_ ∧
    measurementCount (renameProgram _ (basePacket divide j))=_
  rw [renamed.1,renamed.2]
  simp only [basePacket,toffoliCount_append,measurementCount_append,body] at *
  constructor <;> omega


theorem groups_counts (divide : Bool) (j n : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (groups divide j n)=n*6410 ∧ measurementCount (groups divide j n)=n*5121 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_counts divide j hn ho
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append] at head rest ⊢
    all_goals constructor <;> omega


theorem firstSwap_counts : toffoliCount firstSwap=257 ∧ measurementCount firstSwap=1 := by
  have len := BalancedCleanup.widths (Q6EndpointCell.ports base (base 2409)).toLayout (Q6EndpointCell.ports_widths base (base 2409))
  have sp := swapRegisters_resources (base 2409) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y (len.2.1.trans len.2.2.1.symm) base_sign_nd
  have w := transcriptSelectWindow_counts (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (swapRegisters (base 2409) (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y)
  simp only [firstSwap,OneFlagCell.selectSwap,w.1,w.2,sp.1,sp.2.1,len.2.1]
  decide

theorem firstSwapM_counts : toffoliCount firstSwapM=1 ∧ measurementCount firstSwapM=257 := by
  have len := BalancedCleanup.widths (Q6EndpointCell.ports base (base 2409)).toLayout (Q6EndpointCell.ports_widths base (base 2409))
  have sp := UncompSwap.mswap_counts (base 2409) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y (len.2.1.trans len.2.2.1.symm)
  have w := transcriptSelectWindow_counts (base 2400) (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (UncompSwap.mswap (base 2409) (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y)
  simp only [firstSwapM,OneFlagCell.selectMSwap,w.1,w.2,sp.1,sp.2,len.2.1]
  decide

theorem firstPacket_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (firstPacket divide)=(if divide then 5389 else 5133) ∧
      measurementCount (firstPacket divide)=(if divide then 4099 else 4355) := by
  have raw := raw_counts divide Replay5.restLetters (q7part4_swap_nodup hn ho)
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at raw
  have sw := firstSwap_counts
  have swM := firstSwapM_counts
  have e := History5.encode_counts base 0
  have d := History5.decode_counts base 0
  have renamed := renameProgram_counts (shifted (Placement5.pi 0)) (baseFirstPacket divide)
  change toffoliCount (renameProgram _ (baseFirstPacket divide))=_ ∧
    measurementCount (renameProgram _ (baseFirstPacket divide))=_
  rw [renamed.1,renamed.2]
  cases divide <;> simp only [baseFirstPacket,firstBody,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at raw ⊢
  all_goals constructor <;> omega


theorem replay_counts_eq (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (replay divide)=toffoliCount (Q6EndpointReplay.replay divide) ∧
      measurementCount (replay divide)=measurementCount (Q6EndpointReplay.replay divide) := by
  have a := firstPacket_counts divide hn ho
  have ao := Q6EndpointReplay.firstPacket_counts divide hn ho
  have b := groups_counts divide 1 101 hn ho
  have bo := Q6EndpointReplay.groups_counts divide 1 101 hn ho
  have c : endPacket divide=Q6EndpointReplay.endPacket divide := rfl
  cases divide <;> simp only [replay,Q6EndpointReplay.replay,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,logicalReplay,Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,c] at a ao b bo ⊢ <;> constructor <;> omega
end Counts
end ECDSAAdd.Entrant.OneFlagReplay


-- ONEFLAG COMPONENT Structure.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires
private theorem q7part5_rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)


section Physical

theorem raw_physical (divide : Bool) (ls : List MixedTranscriptLetter)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls) :
    GatePhysical (rawReplay divide ls) := by
  induction ls with
  | nil => simp [rawReplay,GatePhysical]
  | cons l ls ih =>
    have nd : [base 2400,l.1.1,l.1.2,base 2409,base 2410].Nodup := by
      simpa only [List.take_succ_cons,List.take_zero] using
        (show ((base 2400::l.1.1::l.1.2::base 2409::base 2410::(skywalkSharedField base).wires).take 5).Nodup
          from (hf l (by simp)).controls.take)
    have cell := OneFlagCell.physical divide base base_injective (base 2400) l.1.1 l.1.2
      l.2.1 l.2.2 (by
        apply List.nodup_iff_count.mpr
        intro q
        have h := List.nodup_iff_count.mp nd q
        simp only [List.count_cons,List.count_nil] at h ⊢
        omega) (by
        apply List.nodup_iff_count.mpr
        intro q
        have h := List.nodup_iff_count.mp nd q
        simp only [List.count_cons,List.count_nil] at h ⊢
        omega) base_sign_nd
    have rest := ih (fun k hk => hf k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append] at cell rest ⊢
    · exact ⟨rest,cell⟩
    · exact ⟨cell,rest⟩

theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters j)) :
    GatePhysical (packet divide j) := by
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have raw : GatePhysical (body divide j) := raw_physical divide _ hn ho hf
  have p : GatePhysical (basePacket divide j) := by
    simpa only [basePacket,gatePhysical_append] using And.intro (And.intro d raw) e
  exact gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ p

theorem groups_physical (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters k)) :
    GatePhysical (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,GatePhysical]
  | succ n ih =>
    have head := packet_physical divide j (by omega) hn ho (hf j (by omega))
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem firstPacket_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (firstPacket divide) := by
  have swap : GatePhysical firstSwap := by
    simp only [firstSwap,OneFlagCell.selectSwap]
    apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    exact swapRegisters_physical _ _ _ base_sign_nd
  have swapM : GatePhysical firstSwapM := by
    unfold firstSwapM OneFlagCell.selectMSwap
    apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    exact UncompSwap.mswap_physical _ _ _ base_sign_nd
  have rest := raw_physical divide Replay5.restLetters hn ho (q7part5_rest_layout hf)
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have p : GatePhysical (baseFirstPacket divide) := by
    cases divide <;> simp only [baseFirstPacket,firstBody,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨⟨d,⟨rest,swapM⟩⟩,e⟩
    · exact ⟨⟨d,⟨swap,rest⟩⟩,e⟩
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ p

theorem endPacket_physical (divide : Bool) : GatePhysical (endPacket divide) :=
  gatePhysical_rename _ (shifted Placement5.pi0).injective _
    (Q6EndpointCell.endpoint_physical divide base base_injective (base 2400) (base 510)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (by decide))

theorem replay_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (replay divide) := by
  have first := firstPacket_physical divide hn ho hf
  have rest := groups_physical divide 1 101 (by decide) hn ho (Replay5.letters_layouts hf)
  have last := endPacket_physical divide
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by decide))
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,rest⟩,first⟩
  · exact ⟨⟨first,rest⟩,last⟩

end Physical

section Slots
open Challenge Baselines
attribute [local irreducible] gateSlots

theorem raw_gateSlots_le (divide : Bool) (ls : List MixedTranscriptLetter) :
    gateSlots (rawReplay divide ls)≤ls.length*26000 := by
  induction ls with
  | nil => simp [rawReplay]
  | cons l ls ih =>
    have c := OneFlagCell.gateSlots_le divide base (base 2400) l.1.1 l.1.2 (base 2409) l.2.1 l.2.2
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append,List.length_cons] at c ih ⊢ <;> omega

theorem packet_gateSlots_le (divide : Bool) (j : Nat) : gateSlots (packet divide j)≤130356 := by
  have raw : gateSlots (body divide j)≤5*26000 := by
    simpa only [Replay5.letters,List.length_map,List.length_range] using
      raw_gateSlots_le divide (Replay5.letters j)
  have codec := History5.codec_slots base (5*j)
  simp only [packet,rename_gateSlots,basePacket,gateSlots_append]
  omega

theorem groups_gateSlots_le (divide : Bool) (j n : Nat) : gateSlots (groups divide j n)≤n*130356 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program]
  | succ n ih =>
    have head := packet_gateSlots_le divide j
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem firstPacket_gateSlots_le (divide : Bool) : gateSlots (firstPacket divide)≤105388 := by
  have swapM : gateSlots firstSwapM≤1032 := by
    have width := (BalancedCleanup.widths (Q6EndpointCell.ports base (base 2409)).toLayout
      (Q6EndpointCell.ports_widths base (base 2409)))
    have sp := UncompSwap.mswap_slots (base 2409) (Q6EndpointCell.ports base (base 2409)).r
      (Q6EndpointCell.ports base (base 2409)).y (width.2.1.trans width.2.2.1.symm)
    have h := selectWindow_gateSlots_le (base 2400) (base 1028) (base 2409)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (UncompSwap.mswap (base 2409) (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y)
    change gateSlots (transcriptSelectWindow _ _ _ _ _)≤_
    rw [sp,width.2.1] at h
    omega
  have raw := raw_gateSlots_le divide Replay5.restLetters
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at raw
  have codec := History5.codec_slots base 0
  have width := (BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))).2.1
  have swap : gateSlots firstSwap≤800 := by
    have h := selectWindow_gateSlots_le (base 2400) (base 1028) (base 2409)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters (base 2409) (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y)
    rw [swapRegisters_gateSlots,width] at h
    simpa only [firstSwap,OneFlagCell.selectSwap,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y] using h.trans (by decide)
  cases divide <;> simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem endPacket_gateSlots_le (divide : Bool) : gateSlots (endPacket divide)≤26000 := by
  simpa only [endPacket,rename_gateSlots,rawEnd] using
    Q6EndpointCell.endpoint_gateSlots_le divide base (base 2400) (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1

theorem replay_gateSlots_le (divide : Bool) : gateSlots (replay divide)≤13941000 := by
  have first := firstPacket_gateSlots_le divide
  have rest := groups_gateSlots_le divide 1 101
  have last := endPacket_gateSlots_le divide
  cases divide <;> simp only [replay,rename_gateSlots,logicalReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append]
    at first rest last ⊢ <;> omega

end Slots

end ECDSAAdd.Entrant.OneFlagReplay


-- ONEFLAG COMPONENT Support.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagCell
open Arithmetic MappedCompressed
attribute [local irreducible] wires Q6EndpointCell.half

theorem window_wires (b source flag : Wire) (constant : Bool) (P : Program) :
    wires (transcriptSelectWindow b source flag constant P)=[b,source,flag].toFinset∪wires P := by
  cases constant <;> ext q <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] <;> tauto

theorem swap_wires (w : Nat → Wire) (flag c : Wire) :
    wires (swapRegisters c (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y)=
      (c::((Q6EndpointCell.ports w flag).r++(Q6EndpointCell.ports w flag).y)).toFinset := by
  have len := BalancedCleanup.widths (Q6EndpointCell.ports w flag).toLayout (Q6EndpointCell.ports_widths w flag)
  have r : (Q6EndpointCell.ports w flag).r.isEmpty=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have z := List.isEmpty_iff.mp h
    have k := len.2.1
    rw [z] at k
    contradiction
  have y : (Q6EndpointCell.ports w flag).y.isEmpty=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have z := List.isEmpty_iff.mp h
    have k := len.2.2.1
    rw [z] at k
    contradiction
  have a := copyRegister_wires none (Q6EndpointCell.ports w flag).y (Q6EndpointCell.ports w flag).r
    (len.2.2.1.trans len.2.1.symm)
  have b := copyRegister_wires (some c) (Q6EndpointCell.ports w flag).r (Q6EndpointCell.ports w flag).y
    (len.2.1.trans len.2.2.1.symm)
  simp only [swapRegisters,wires_append,a,b,r,y,Bool.false_eq_true,if_false,Option.toList_none,
    Option.toList_some,List.nil_append]
  ext q
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

theorem cell_wires_subset_old (divide : Bool) (w : Nat → Wire) (b g sw flag eff : Wire) (ig is : Bool) :
    wires (cell divide w b g sw flag ig is)⊆wires (Q6EndpointCell.cell divide w b g sw flag eff ig is) := by
  have a := swap_wires w flag flag
  have z := swap_wires w flag eff
  cases divide <;> simp only [cell,halfWindow,selectSwap,Q6EndpointCell.cell,Q6EndpointCell.body,
    Bool.false_eq_true,if_false,if_true,window_wires,wires_append,a,z]
  all_goals
    intro q h
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil] at h ⊢
    tauto
end ECDSAAdd.Entrant.OneFlagCell

namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic MappedCompressed
attribute [local irreducible] wires Q6EndpointCell.half

theorem rename_subset (f : Wire→Wire) (P Q : Program) (h : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  simp only [renameProgram_support]
  exact Finset.image_subset_image h

theorem raw_wires_subset_old (divide : Bool) (ls : List MixedTranscriptLetter) :
    wires (rawReplay divide ls)⊆wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [rawReplay,Q6EndpointReplay.rawReplay]
  | cons l ls ih =>
    have c := OneFlagCell.cell_wires_subset_old divide base (base 2400) l.1.1 l.1.2
      (base 2409) (base 2410) l.2.1 l.2.2
    cases divide <;> simp only [rawReplay,Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append] at c ih ⊢
    · exact Finset.union_subset_union ih c
    · exact Finset.union_subset_union c ih

theorem old_raw_flag_mem (divide : Bool) (ls : List MixedTranscriptLetter) (h : ls≠[]) :
    base 2409∈wires (Q6EndpointReplay.rawReplay divide ls) := by
  cases ls with
  | nil => exact False.elim (h rfl)
  | cons l ls =>
    have c : base 2409∈wires (Q6EndpointCell.cell divide base (base 2400) l.1.1 l.1.2
        (base 2409) (base 2410) l.2.1 l.2.2) := by
      rw [Q6EndpointCell.cell,OneFlagCell.window_wires]
      exact Finset.mem_union_left _ (by simp)
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append] at c ⊢
    · exact Finset.mem_union_right _ c
    · exact Finset.mem_union_left _ c

theorem firstSwap_subset_old : wires firstSwap⊆wires Replay5.firstSwap∪{base 2409} := by
  have a := OneFlagCell.swap_wires base (base 2409) (base 2409)
  have z := OneFlagCell.swap_wires base (base 2409) (base 2410)
  simp only [firstSwap,OneFlagCell.selectSwap,Replay5.firstSwap,EntryFieldSeedCancellation.selectedSwap,
    OneFlagCell.window_wires,←Q6EndpointCell.ports_r base (base 2409),←Q6EndpointCell.ports_y base (base 2409),a,z]
  intro q h
  simp only [Finset.mem_union,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,List.mem_append,
    List.not_mem_nil] at h ⊢
  tauto

theorem firstSwapM_subset_old : wires firstSwapM⊆wires UncompSwap.firstSwapM∪{base 2409} := by
  change wires (OneFlagCell.selectMSwap _ _ _ _ _)⊆_
  rw [OneFlagCell.selectMSwap_wires,UncompSwap.firstSwapM_wires]
  exact firstSwap_subset_old

theorem firstBody_subset_old (divide : Bool) : wires (firstBody divide)⊆wires (Q6EndpointReplay.firstBody divide) := by
  have a := raw_wires_subset_old divide Replay5.restLetters
  have flag := old_raw_flag_mem divide Replay5.restLetters (by simp [Replay5.restLetters])
  have s := firstSwap_subset_old
  have m := firstSwapM_subset_old
  cases divide <;> simp only [firstBody,Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append] at a flag ⊢
  · intro q h
    rcases Finset.mem_union.mp h with h|h
    · exact Finset.mem_union_left _ (a h)
    · rcases Finset.mem_union.mp (m h) with h|h
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ ((Finset.mem_singleton.mp h) ▸ flag)
  · intro q h
    rcases Finset.mem_union.mp h with h|h
    · rcases Finset.mem_union.mp (s h) with h|h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ ((Finset.mem_singleton.mp h) ▸ flag)
    · exact Finset.mem_union_right _ (a h)

theorem packet_subset_old (divide : Bool) (j : Nat) : wires (packet divide j)⊆wires (Q6EndpointReplay.packet divide j) := by
  apply rename_subset
  simp only [basePacket,Q6EndpointReplay.basePacket,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (raw_wires_subset_old divide _))
    (Finset.Subset.refl _)

theorem firstPacket_subset_old (divide : Bool) : wires (firstPacket divide)⊆wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_subset
  simp only [baseFirstPacket,Q6EndpointReplay.baseFirstPacket,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (firstBody_subset_old divide))
    (Finset.Subset.refl _)

theorem groups_subset_old (divide : Bool) (j n : Nat) :
    wires (groups divide j n)⊆wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,Q6EndpointReplay.groups,PacketSequence.program]
  | succ n ih =>
    have a := packet_subset_old divide j
    have b := ih (j+1)
    cases divide <;> simp only [groups,Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append] at b ⊢
    · exact Finset.union_subset_union b a
    · exact Finset.union_subset_union a b

theorem replay_subset_old (divide : Bool) : wires (replay divide)⊆wires (Q6EndpointReplay.replay divide) := by
  have a := firstPacket_subset_old divide
  have b := groups_subset_old divide 1 101
  have c : endPacket divide=Q6EndpointReplay.endPacket divide := rfl
  apply rename_subset
  cases divide <;> simp only [logicalReplay,Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,wires_append,c]
  · exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) b) a
  · exact Finset.union_subset_union (Finset.union_subset_union a b) (Finset.Subset.refl _)
end ECDSAAdd.Entrant.OneFlagReplay

namespace ECDSAAdd.Entrant.OneFlagReplay
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run

theorem field_frame_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : FieldFrameOB5.EncodedFieldFrame origin X Y s)
    (ht : FieldFrameOB5.EncodedFieldFrame origin X Y t) (phase : s.phase=t.phase) : s=t := by
  have e := EntryFuse.encoded_field_unique5 origin X Y (pullState (OB5.sig 511) s)
    (pullState (OB5.sig 511) t) hs ht phase
  apply State.extensionality s t phase
  funext q
  have h := congrArg (fun a:State=>a.basis (OB5.sig 511 q)) e
  simpa only [pullState,OB5.sig_invol 511 (by decide)] using h

theorem forward_state_eq (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    run (replay true) m s=run (Q6EndpointReplay.replay true) m s := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  have a := forward_frame origin ctx x hx0 hx trace Y s m input
  have b := Q6EndpointReplay.forward_frame origin oldctx x hx0 hx trace Y s m input
  exact field_frame_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem inverse_state_eq (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    run (replay false) m s=run (Q6EndpointReplay.replay false) m s := by
  let oldctx : Q6EndpointReplay.Context origin :=
    ⟨ctx.hn,ctx.ho,ctx.hp,ctx.hf,ctx.hg0,ctx.hs0,ctx.env,ctx.legal,ctx.parity⟩
  have a := inverse_frame origin ctx x hx0 hx trace Y s m input
  have b := Q6EndpointReplay.inverse_frame origin oldctx x hx0 hx trace Y s m input
  exact field_frame_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)
end ECDSAAdd.Entrant.OneFlagReplay


-- ONEFLAG COMPONENT Segment.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagSegment
open Arithmetic Secp256k1 BalancedField MappedCompressed OffsetBorrowedCanonical History5 HalfFieldOB5
attribute [local irreducible] run wires HalfFieldOB5.centerT HalfFieldOB5.canonT OneFlagReplay.replay

def program (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(OneFlagReplay.replay true++(copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(copyN++(OneFlagReplay.replay false++OwnQ5Endpoint.canonT))

private theorem q7part7_run_four_states (a b c d : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 : State) (m1 m2 m3 m4 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → run d m4 s3=s4 → P s s4)
    (s : State) (m : List Bool) : P s (run (a++(b++(c++d))) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

private theorem q7part7_double_half (Y W : Fp) : 2*(Y/2*W)=Y*W := by
  have two : (2:Fp) ≠ 0 := by decide
  field_simp

private theorem q7part7_double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp) ≠ 0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem q7part7_double_half_one (Y : Fp) : 2*(Y/2)=Y := by
  have two : (2:Fp) ≠ 0 := by decide
  exact mul_div_cancel₀ Y two

/-- Same hypotheses and conclusion as the protected selected field segment. -/
theorem program_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let out := run (program divide) m s
    out.phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let ctx : OneFlagReplay.Context origin := ⟨hn,ho,hp,hf,hg0,hs0,env,legal,hr⟩
  cases divide
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out
    have all := q7part7_run_four_states OwnQ5Endpoint.centerT copyN (OneFlagReplay.replay false) OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := copy_fill hn origin (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := OneFlagReplay.inverse_frame origin ctx
        x hx0 hx trace (Y/2) s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y := by
        unfold fieldResult
        split
        · simp only [Bool.false_eq_true,if_false]; exact q7part7_double_half Y _
        · exact q7part7_double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,Bool.false_eq_true,if_false] using all input
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out
    have all := q7part7_run_four_states OwnQ5Endpoint.centerT (OneFlagReplay.replay true) copyN OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := OneFlagReplay.forward_frame origin ctx x hx0 hx trace
        (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := copy_clear hn origin _ s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2/(x:Fp) else Y/2)=fieldResult true origin x Y := by
        unfold fieldResult
        split
        · simp only [if_true]; exact q7part7_double_half_div Y _
        · exact q7part7_double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,if_true] using all input

theorem counts_eq (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (program divide)=toffoliCount (Q6EndpointSegment.program divide) ∧
      measurementCount (program divide)=measurementCount (Q6EndpointSegment.program divide) := by
  have r := OneFlagReplay.replay_counts_eq divide hn ho
  cases divide <;> simp only [program,Q6EndpointSegment.program,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at r ⊢ <;> constructor <;> omega

theorem subset_old (divide : Bool) : wires (program divide)⊆wires (Q6EndpointSegment.program divide) := by
  have r := OneFlagReplay.replay_subset_old divide
  cases divide <;> simp only [program,Q6EndpointSegment.program,Bool.false_eq_true,if_false,if_true,wires_append]
  · exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union r (Finset.Subset.refl _)))
  · exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union r (Finset.Subset.refl _))

theorem physical (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (program divide) := by
  have c := OwnQ5Endpoint.endpoint_physical hn
  have r := OneFlagReplay.replay_physical divide hn ho hf
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨c.1,c.2.2,r,c.2.1⟩
  · exact ⟨c.1,r,c.2.2,c.2.1⟩

theorem gateSlots_le (divide : Bool) : Challenge.gateSlots (program divide)≤14100000 := by
  have c := OwnQ5Endpoint.endpoint_gateSlots_le
  have r := OneFlagReplay.replay_gateSlots_le divide
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,Challenge.gateSlots_append] <;> omega

theorem endpoint_eff_free : base 2410∉wires OwnQ5Endpoint.centerT ∧ base 2410∉wires OwnQ5Endpoint.canonT := by
  have avoid (P : Program) (hp : wires P⊆(HalfField.ids.map base).toFinset) : base 2410∉wires P := by
    intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp (List.mem_toFinset.mp (hp h))
    have eq := base_injective he
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
    omega
  have h0 := And.intro (avoid _ HalfField.centerT_sites) (avoid _ HalfField.canonT_sites)
  have h1 : base 2410∉wires HalfFieldOB5.centerT ∧ base 2410∉wires HalfFieldOB5.canonT := by
    simpa only [HalfFieldOB5.centerT,HalfFieldOB5.canonT,HalfField5.centerT,HalfField5.canonT] using
      And.intro (OwnPlusHost.rename_avoid HalfFieldOB5.endpointMap (base 2410) HalfField.centerT (by decide) h0.1)
        (OwnPlusHost.rename_avoid HalfFieldOB5.endpointMap (base 2410) HalfField.canonT (by decide) h0.2)
  have h2 : base 2410∉wires OwnPlusEndpoint.centerT ∧ base 2410∉wires OwnPlusEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid OwnPlusEndpoint.swap (base 2410) _ (by decide) h1.1,OwnPlusHost.rename_avoid OwnPlusEndpoint.swap (base 2410) _ (by decide) h1.2⟩
  have h3 : base 2410∉wires OwnGuardEndpoint.centerT ∧ base 2410∉wires OwnGuardEndpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid OwnGuardEndpoint.swap (base 2410) _ (by decide) h2.1,OwnPlusHost.rename_avoid OwnGuardEndpoint.swap (base 2410) _ (by decide) h2.2⟩
  have h4 : base 2410∉wires OwnQ4Endpoint.centerT ∧ base 2410∉wires OwnQ4Endpoint.canonT :=
    ⟨OwnPlusHost.rename_avoid OwnQ4Endpoint.swap (base 2410) _ (by decide) h3.1,OwnPlusHost.rename_avoid OwnQ4Endpoint.swap (base 2410) _ (by decide) h3.2⟩
  exact ⟨OwnPlusHost.rename_avoid OwnQ5Endpoint.swap (base 2410) _ (by decide) h4.1,OwnPlusHost.rename_avoid OwnQ5Endpoint.swap (base 2410) _ (by decide) h4.2⟩

theorem eff_free (divide : Bool) : base 2410∉wires (program divide) := by
  have ep := endpoint_eff_free
  have r := OneFlagReplay.replay_eff_free divide
  have cp : base 2410∉wires copyN := by decide +kernel
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,wires_append,Finset.mem_union,not_or]
    at r ⊢
  · exact ⟨ep.1,cp,r,ep.2⟩
  · exact ⟨ep.1,r,cp,ep.2⟩

def segH (divide : Bool) : Program := [.X (base 511)] ++
  (renameProgram HostOB5.hostSwap (program divide) ++ [.X (base 511)])

theorem hosted1542_free (divide : Bool) : base 1542∉wires (segH divide) := by
  have h := OneFlagReplay.rename_free HostOB5.hostSwap HostOB5.hostSwap_injective
    (base 1542) (base 2410) (by decide) (program divide) (eff_free divide)
  simpa only [segH,wires_append,wires,Instr.wires,Finset.union_empty,Finset.mem_union,
    Finset.mem_singleton,not_or] using And.intro (by decide : base 1542≠base 511)
      (And.intro h (by decide : base 1542≠base 511))
theorem canonical_frame_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : FieldFrameOB5.EncodedCanonicalFrame origin X Y s)
    (ht : FieldFrameOB5.EncodedCanonicalFrame origin X Y t) (phase : s.phase=t.phase) : s=t := by
  have e := History5.encoded_canonical_unique origin X Y (pullState (OB5.sig 511) s)
    (pullState (OB5.sig 511) t) hs ht phase
  apply State.extensionality s t phase
  funext q
  have h := congrArg (fun a:State=>a.basis (OB5.sig 511 q)) e
  simpa only [pullState,OB5.sig_invol 511 (by decide)] using h

theorem program_state_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    run (program divide) m s=run (Q6EndpointSegment.program divide) m s := by
  have a := program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have b := Q6EndpointSegment.program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  exact canonical_frame_unique origin _ _ _ _ a.2 b.2 (a.1.trans b.1.symm)

theorem segH_subset_old (divide : Bool) : wires (segH divide)⊆wires ([.X (base 511)] ++ (renameProgram HostOB5.hostSwap (Q6EndpointSegment.program divide) ++ [.X (base 511)])) := by
  have h := OneFlagReplay.rename_subset HostOB5.hostSwap _ _ (subset_old divide)
  simp only [segH,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))

theorem segH_counts_eq (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (segH divide)=toffoliCount ([.X (base 511)] ++ (renameProgram HostOB5.hostSwap (Q6EndpointSegment.program divide) ++ [.X (base 511)])) ∧
      measurementCount (segH divide)=measurementCount ([.X (base 511)] ++ (renameProgram HostOB5.hostSwap (Q6EndpointSegment.program divide) ++ [.X (base 511)])) := by
  have h := counts_eq divide hn ho
  simpa only [segH,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,toffoliCount,measurementCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.zero_add,Nat.add_zero] using h

end ECDSAAdd.Entrant.OneFlagSegment


-- ONEFLAG COMPONENT IntegerHostEndpointQ7.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q7IntegerHost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk OffsetBorrowedCanonical History5
attribute [local irreducible] wires run Stack5.forward5 stackForwardT NativeFirstDirect.forward StackOB5.forward OB5.sig
def swap : Equiv.Perm Wire := Equiv.swap (base 1542) (base 720)

theorem pull_clean (s : State) (a : s.basis (base 1542)=false)
    (b : s.basis (base 720)=false) : pullState swap s=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (swap q)=s.basis q
    by_cases h : q=base 1542
    · subst q; simp [swap,a,b]
    · by_cases h' : q=base 720
      · subst q; simp [swap,a,b]
      · rw [show swap q=q by exact Equiv.swap_apply_of_ne_of_ne h h']

theorem run_eq (P : Program) (s : State) (m : List Bool)
    (a : s.basis (base 1542)=false) (b : s.basis (base 720)=false)
    (c : (run P m s).basis (base 1542)=false)
    (d : (run P m s).basis (base 720)=false) :
    run (renameProgram swap P) m s=run P m s := by
  apply pullState_perm_injective swap
  rw [run_rename swap swap.injective,pull_clean s a b,pull_clean _ c d]


theorem integer720_free : base 720∉OB5.integerSites := by
  intro used
  obtain ⟨i,e,hi⟩ := (OB5.integerSites_mem _).mp used
  have same := base_injective e
  omega

theorem prefix720_free : base 720∉NativeFirstDirect.prefixSites base := by
  intro used
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with ((a|b)|c)|(a|b)
  · exact OwnPlusHost.not_block 720 0 257 (by omega) a
  · exact OwnPlusHost.not_block 720 770 258 (by omega) b
  · exact OwnPlusHost.not_block 720 1540 256 (by omega) c
  · exact (by decide : base 720≠base 1028) a
  · exact (by decide : base 720≠base 1797) b

theorem terminal1542 (x : Nat) (s : State)
    (h : W.CompressedCompactStage5 base x p 512 s.basis) :
    s.basis (base 1542)=false := by
  obtain ⟨raw,stage,eq⟩ := h
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have carry : regValue (wireBlock base 1540 257) raw.basis=0 := fields.2.2.2.2.2.1
  have clean : raw.basis (base 1542)=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have away : base 1542∉wires (History5.encodePrefix base 512) := by
    rw [History5.encodePrefix_512]
    intro used
    have support := History5.allEncode_history_support base 102 (by decide) used
    simp only [List.mem_toFinset,List.mem_append] at support
    rcases support with a|b
    · exact OwnPlusHost.not_block 1542 0 512 (by omega) a
    · exact OwnPlusHost.not_block 1542 1028 512 (by omega) b
  rw [eq,run_preserves_outside _ [] raw _ away]
  exact clean
theorem terminalS511 (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State)
    (h : W.CompressedCompactStage5 base x p 512 s.basis) : s.basis (base 1539)=false := by
  obtain ⟨raw,stage,eq⟩ := h
  have fields := (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup raw.basis).mp stage
  have bit := (fields.2.2.2.1 511 (by omega)).2
  rw [SkywalkTrace.code511 x hx0 hx] at bit
  have away : base 1539∉wires (History5.encodePrefix base 512) := by
    rw [History5.encodePrefix_512]
    intro used
    obtain ⟨j,hj,mem⟩:=History5.allEncode_member base 102 _ used
    obtain ⟨i,e⟩:=History5.history_gate_mem base (5*j) _ (Or.inl rfl) _ mem
    change base 1539=base (History5.historyId (5*j) i) at e
    have same:=base_injective e
    have hi:=i.isLt
    unfold History5.historyId at same
    split_ifs at same <;> omega
  rw [eq,run_preserves_outside _ [] raw _ away]
  exact bit

theorem forward_terminal1542 (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (m2 : List Bool)
    (firstW : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis) :
    (run stackForwardT m2 s1).basis (base 1542)=false := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  obtain ⟨t, ht⟩ : ∃t : State,run (Stack5.forward5 base 1 511) m2 s1=t := ⟨_,rfl⟩
  have terminal : W.CompressedCompactStage5 base x p 512 t.basis := by
    have raw := (Stack5.forward_spec base base_pool_nodup StackOB5.historyAbove x p 1 511
      hp0 hx0 hpo hp gap hx cop (by omega) s1 m2 (W.compactStage5_first base x p s1 firstW)).2
    rw [ht] at raw
    exact raw
  have eq : run stackForwardT m2 s1 = pullState (OB5.sig 511) t := by
    rw [←ht]
    exact (stackForwardT_run hn StackOB5.historyAbove x hx0 hx s1 m2 firstW).trans
      (StackOB5.forward_run x hx0 hx s1 m2 firstW)
  have fixed : OB5.sig 511 (base 1542)=base 1539 := by decide +kernel
  rw [eq]
  change t.basis (OB5.sig 511 (base 1542))=false
  rw [fixed]
  exact terminalS511 x hx0 hx _ terminal

theorem history1542_free (start : Nat) (hs : start+5≤512) (q : Fin 10) :
    History5.historyId start q ≠1542 := by
  have h:=History5.historyId_region start hs q
  omega

theorem sig1542_last : OB5.sig 511 (base 1542)=base 1539 := by decide +kernel


def firstPhase : Program := NativeFirstDirect.forward base ++ (stackForwardT ++ skywalkArithmeticClear base)
attribute [local irreducible] firstPhase

theorem firstPhase720_free : base 720∉wires firstPhase := by
  have native : base 720∉wires (NativeFirstDirect.forward base) := fun h =>
    prefix720_free (List.mem_toFinset.mp ((NativeFirstDirect.prefix_support base).1 h))
  have stack : base 720∉wires stackForwardT := fun h =>
    integer720_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).1 _ (stackForwardT_subset h))
  have clear : base 720∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [firstPhase,wires_append,Finset.mem_union,not_or] using ⟨native,stack,clear⟩

theorem input_clean (x y i : Nat) (s : State) (hin : SkywalkArithmeticInput base x y s.basis)
    (hi : i=720 ∨ i=1542) : s.basis (base i)=false := by
  apply hin.2.2 (base i)
  · rcases hi with rfl|rfl <;> decide +kernel
  · exact OwnPlusHost.not_block i 770 256 (by rcases hi with rfl|rfl <;> omega)
  · exact OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem firstPhase1542_clean (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    (run firstPhase m s).basis (base 1542)=false := by
  rw [firstPhase,run_append,run_append]
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s
    (m.take (measurementCount (NativeFirstDirect.forward base))) hin
  have firstW := (W.compactSkywalkStage_one base _ _).mpr first
  have cleaned := forward_terminal1542 hn x hx0 hx _
    ((m.drop (measurementCount (NativeFirstDirect.forward base))).take (measurementCount stackForwardT)) firstW
  have away : base 1542∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  exact (run_preserves_outside _ _ _ _ away).trans cleaned

theorem firstPhase_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap firstPhase) m s=run firstPhase m s := by
  apply run_eq
  · exact input_clean x Y.val 1542 s hin (Or.inr rfl)
  · exact input_clean x Y.val 720 s hin (Or.inl rfl)
  · exact firstPhase1542_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ firstPhase720_free).trans
      (input_clean x Y.val 720 s hin (Or.inl rfl))
def lastPhase : Program := skywalkArithmeticClear base ++ (stackReverseT ++ NativeFirstKnown.inverse base)
attribute [local irreducible] lastPhase

theorem lastPhase720_free : base 720∉wires lastPhase := by
  have native : base 720∉wires (NativeFirstKnown.inverse base) := fun h =>
    prefix720_free (List.mem_toFinset.mp (NativeFirstKnown.inverse_support base h))
  have stack : base 720∉wires stackReverseT := fun h =>
    integer720_free ((StackOB5.support_gen 1 511 (by omega) (by omega)).2 _ (stackReverseT_subset h))
  have clear : base 720∉wires (skywalkArithmeticClear base) := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,wires,Instr.wires,base]
  simpa only [lastPhase,wires_append,Finset.mem_union,not_or] using ⟨clear,stack,native⟩

/-- Full arbitrary-record transfer needs only the old complete program's clean
output and the new field implementation's literal omission of1542. It imposes
no new promise on the original caller input. -/
theorem three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1542∉wires F)
    (out1542 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 1542)=false)
    (out720 : (run lastPhase mr (run F mf (run firstPhase mp s))).basis (base 720)=false) :
    run (renameProgram swap lastPhase) mr
      (run F mf (run (renameProgram swap firstPhase) mp s)) =
    run lastPhase mr (run F mf (run firstPhase mp s)) := by
  rw [firstPhase_state_eq hn x Y hx0 hx s mp hin]
  have mid1542 : (run F mf (run firstPhase mp s)).basis (base 1542)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1542_clean hn x Y hx0 hx s mp hin)
  have mid720 : (run F mf (run firstPhase mp s)).basis (base 720)=false :=
    (run_preserves_outside lastPhase mr _ _ lastPhase720_free).symm.trans out720
  exact run_eq lastPhase _ mr mid1542 mid720 out1542 out720

theorem wireFn2_720 (L : ControlledPointLayout) : wireFn2 L (base 720)=L.core.poolWire 720 := by rfl

theorem rename_1542_free (P : Program) (free : base 720∉wires P) :
    base 1542∉wires (renameProgram swap P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,member,eq⟩ := Finset.mem_image.mp used
  have back := congrArg swap eq
  simp only [swap,Equiv.swap_apply_self,Equiv.swap_apply_left] at back
  exact free (back ▸ member)

theorem wireFn2_1542 (L : ControlledPointLayout) : wireFn2 L (base 1542)=L.core.poolWire 1286 := by rfl

theorem final720_charged (L : ControlledPointLayout) : L.core.poolWire 720∈WrapperOB5.sites L := by
  have member : L.core.poolWire 720∈wireBlock L.core.poolWire 718 311 :=
    List.mem_map.mpr ⟨720,by simp only [List.mem_range'_1]; omega,rfl⟩
  simp only [WrapperOB5.sites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto


def q5First : Program := renameProgram Q5Global718.swap firstPhase
def q5Last : Program := renameProgram Q5Global718.swap lastPhase
attribute [local irreducible] q5First q5Last

theorem q5first_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run q5First m s=run firstPhase m s := by
  have same : firstPhase=Q5Global718.firstPhase := by unfold firstPhase Q5Global718.firstPhase; rfl
  unfold q5First
  rw [same]
  exact Q5Global718.firstPhase_state_eq hn x Y hx0 hx s m hin

theorem q5First720_free : base 720∉wires q5First := by
  unfold q5First
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) firstPhase720_free

theorem q5Last720_free : base 720∉wires q5Last := by
  unfold q5Last
  exact OwnPlusHost.rename_avoid _ _ _ (by decide +kernel) lastPhase720_free

theorem q5First_state_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis) :
    run (renameProgram swap q5First) m s=run q5First m s := by
  apply run_eq
  · exact input_clean x Y.val 1542 s hin (Or.inr rfl)
  · exact input_clean x Y.val 720 s hin (Or.inl rfl)
  · rw [q5first_eq hn x Y hx0 hx s m hin]
    exact firstPhase1542_clean hn x Y hx0 hx s m hin
  · exact (run_preserves_outside _ _ _ _ q5First720_free).trans
      (input_clean x Y.val 720 s hin (Or.inl rfl))

theorem q5_three_states_eq (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (mp mf mr : List Bool) (F : Program)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (field_free : base 1542∉wires F)
    (out1542 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 1542)=false)
    (out720 : (run q5Last mr (run F mf (run q5First mp s))).basis (base 720)=false) :
    run (renameProgram swap q5Last) mr
      (run F mf (run (renameProgram swap q5First) mp s)) =
    run q5Last mr (run F mf (run q5First mp s)) := by
  rw [q5First_state_eq hn x Y hx0 hx s mp hin]
  have mid1542 : (run F mf (run q5First mp s)).basis (base 1542)=false := by
    rw [run_preserves_outside _ _ _ _ field_free,q5first_eq hn x Y hx0 hx s mp hin]
    exact firstPhase1542_clean hn x Y hx0 hx s mp hin
  have mid720 : (run F mf (run q5First mp s)).basis (base 720)=false :=
    (run_preserves_outside q5Last mr _ _ q5Last720_free).symm.trans out720
  exact run_eq q5Last _ mr mid1542 mid720 out1542 out720

end ECDSAAdd.Entrant.Q7IntegerHost


-- ONEFLAG COMPONENT FusionPhaseQ7.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q7FusionPhase
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed DirectSkywalk CompressedAllocation Q7IntegerHost
def q6First : Program := renameProgram Q6IntegerHost.swap Q6IntegerHost.q5First
def q6Last : Program := renameProgram Q6IntegerHost.swap Q6IntegerHost.q5Last
attribute [local irreducible] run wires q6First q6Last

theorem q6First720_free : base 720∉wires q6First := by
 have old : base 720∉wires Q6IntegerHost.q5First := by
  simpa only [Q6IntegerHost.q5First,Q7IntegerHost.q5First,Q6IntegerHost.firstPhase,Q7IntegerHost.firstPhase] using
    Q7IntegerHost.q5First720_free
 simpa only [q6First] using OwnPlusHost.rename_avoid Q6IntegerHost.swap _ _ (by decide +kernel) old

theorem q6Last720_free : base 720∉wires q6Last := by
 have old : base 720∉wires Q6IntegerHost.q5Last := by
  simpa only [Q6IntegerHost.q5Last,Q7IntegerHost.q5Last,Q6IntegerHost.lastPhase,Q7IntegerHost.lastPhase] using
    Q7IntegerHost.q5Last720_free
 simpa only [q6Last] using OwnPlusHost.rename_avoid Q6IntegerHost.swap _ _ (by decide +kernel) old

theorem outside_num (i : Nat) (hi : i=720∨i=1542) : base i∉wireBlock base 2056 256 :=
  OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)

theorem q6First_pool : wires q6First⊆(skywalkPoolWires base).toFinset := by
 unfold q6First
 rw [renameProgram_support]
 intro q h
 obtain ⟨old,used,rfl⟩:=Finset.mem_image.mp h
 have oldPool := Q6FusionPhase.q5First_pool used
 by_cases a:old=base 1541
 · subst old
   apply List.mem_toFinset.mpr
   simpa only [Q6IntegerHost.swap,Equiv.swap_apply_left] using arith_mem base 0 1798 719 (by omega) (by omega)
 · by_cases b:old=base 719
   · subst old
     apply List.mem_toFinset.mpr
     simpa only [Q6IntegerHost.swap,Equiv.swap_apply_right] using arith_mem base 0 1798 1541 (by omega) (by omega)
   · simpa only [Q6IntegerHost.swap,Equiv.swap_apply_of_ne_of_ne a b] using oldPool

theorem firstPhase1542_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    (run q6First m b).basis (base 1542)=false := by
  have agree := Q5FusionPhase.pool_agreement q6First q6First_pool a b m same (base 1542)
    (arith_mem base 0 1798 1542 (by omega) (by omega))
  have canonical : run q6First m a=run Q7IntegerHost.firstPhase m a := by
    unfold q6First
    rw [Q6IntegerHost.q5First_state_eq hn x Y hx0 hx a m input]
    change run Q7IntegerHost.q5First m a=run Q7IntegerHost.firstPhase m a
    exact Q7IntegerHost.q5first_eq hn x Y hx0 hx a m input
  exact agree.trans (canonical ▸ Q7IntegerHost.firstPhase1542_clean hn x Y hx0 hx a m input)

theorem firstPhase_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b) :
    run (renameProgram swap q6First) m b=run q6First m b := by
  have clean1542 : b.basis (base 1542)=false :=
    (same _ (outside_num 1542 (Or.inr rfl))).trans (input_clean x Y.val 1542 a input (Or.inr rfl))
  have clean720 : b.basis (base 720)=false :=
    (same _ (outside_num 720 (Or.inl rfl))).trans (input_clean x Y.val 720 a input (Or.inl rfl))
  exact run_eq q6First b m clean1542 clean720
    (firstPhase1542_paired hn x Y hx0 hx a b m input same)
    ((run_preserves_outside _ _ _ _ q6First720_free).trans clean720)

theorem three_states_eq_paired (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (mp mf mr : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1542∉wires F)
    (out1542 : (run q6Last mr (run F mf (run q6First mp b))).basis (base 1542)=false)
    (out720 : (run q6Last mr (run F mf (run q6First mp b))).basis (base 720)=false) :
    run (renameProgram swap q6Last) mr (run F mf (run (renameProgram swap q6First) mp b))=
      run q6Last mr (run F mf (run q6First mp b)) := by
  rw [firstPhase_eq_paired hn x Y hx0 hx a b mp input same]
  have mid1542 : (run F mf (run q6First mp b)).basis (base 1542)=false :=
    (run_preserves_outside _ _ _ _ field_free).trans (firstPhase1542_paired hn x Y hx0 hx a b mp input same)
  have mid720 : (run F mf (run q6First mp b)).basis (base 720)=false :=
    (run_preserves_outside q6Last mr _ _ q6Last720_free).symm.trans out720
  exact run_eq q6Last _ mr mid1542 mid720 out1542 out720

def kernel (F : Program) := q6First++(F++q6Last)
def relocated (F : Program) := renameProgram swap q6First++(F++renameProgram swap q6Last)
attribute [local irreducible] kernel relocated

theorem old_shape (F : Program) : kernel F=Q6FusionPhase.relocated F := by
 simp only [kernel,q6First,q6Last,Q6FusionPhase.relocated]

theorem state_eq_of_frame (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (field_free : base 1542∉wires F)
    (frame : ∀q,q∉wireBlock base 2056 256 → (run (kernel F) m b).basis q=a.basis q) :
    run (relocated F) m b=run (kernel F) m b := by
  have clean (i : Nat) (hi : i=720∨i=1542) : (run (kernel F) m b).basis (base i)=false :=
    (frame _ (outside_num i hi)).trans (input_clean x Y.val i a input hi)
  have h:=three_states_eq_paired hn x Y hx0 hx a b
    (m.take (measurementCount q6First))
    ((m.drop (measurementCount q6First)).take (measurementCount F))
    ((m.drop (measurementCount q6First)).drop (measurementCount F)) F input same field_free
    (by simpa only [kernel,run_append] using clean 1542 (Or.inr rfl))
    (by simpa only [kernel,run_append] using clean 720 (Or.inl rfl))
  simpa only [kernel,relocated,run_append,(renameProgram_counts swap q6First).2] using h

theorem relocated_1542_free (F : Program) (field_free : base 1542∉wires F) :
    base 1542∉wires (relocated F) := by
  rw [relocated,wires_append,wires_append]
  simpa only [Finset.mem_union,not_or] using
    ⟨rename_1542_free q6First q6First720_free,field_free,rename_1542_free q6Last q6Last720_free⟩

theorem relocated_counts (F : Program) :
    toffoliCount (relocated F)=toffoliCount (kernel F) ∧
    measurementCount (relocated F)=measurementCount (kernel F) := by
  have a:=renameProgram_counts swap q6First
  have b:=renameProgram_counts swap q6Last
  simp only [kernel,relocated,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  trivial
end ECDSAAdd.Entrant.Q7FusionPhase


-- ONEFLAG COMPONENT SWOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagSW
open ECDSAAdd.Arithmetic MappedCompressed CompressedFieldSupport Secp256k1 DirectSkywalk SW
attribute [local irreducible] wires

/-! ### Definitions -/

def swapBody : Program :=
  swapRegisters (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def cellS (divide : Bool) (g sw : Wire) : Program :=
 if divide then selW g (base 2409) (Q6EndpointCell.half true base (base 2409))++
   selW sw (base 2409) swapBody
 else selW sw (base 2409) swapBody++
   selW g (base 2409) (Q6EndpointCell.half false base (base 2409))

def rawReplayS (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then cellS true l.1.1 l.1.2++rawReplayS true ls
    else rawReplayS false ls++cellS false l.1.1 l.1.2

def basePacketS (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++rawReplayS divide (Replay5.letters j)++History5.encode base (5*j)

def packetS (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacketS divide j)

def groupsS (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (packetS divide) j n

def firstSwapS : Program := selW (base 1028) (base 2409) swapBody

def swapBodyM : Program :=
  UncompSwap.mswap (base 2409) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def firstSwapMS : Program := selW (base 1028) (base 2409) swapBodyM

def firstBodyS (divide : Bool) : Program :=
  if divide then firstSwapS++rawReplayS true Replay5.restLetters
  else rawReplayS false Replay5.restLetters++firstSwapMS

def baseFirstPacketS (divide : Bool) : Program :=
  History5.decode base 0++firstBodyS divide++History5.encode base 0

def firstPacketS (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacketS divide)

def rawEndS (divide : Bool) : Program :=
  selW (base 510) (base 2409) (Q6EndpointCell.halfE divide base (base 2409))

def endPacketS (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEndS divide)

def logicalReplayS (divide : Bool) : Program :=
  if divide then firstPacketS true++groupsS true 1 101++endPacketS true
  else endPacketS false++groupsS false 1 101++firstPacketS false

def replayS (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplayS divide)

def segmentS (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++(replayS false++OwnQ5Endpoint.canonT))

/-- The selector-hosted segment (`KernelOB5.segH`) around the selector-free segment. -/
def segHS (divide : Bool) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap (segmentS divide) ++ [.X (base 511)])

def kernelS (divide : Bool) : Program :=
  NativeFirstDirect.forward base++stackForwardT++skywalkArithmeticClear base++
    segHS divide++skywalkArithmeticClear base++stackReverseT++
      NativeFirstKnown.inverse base

/-! ### Frames -/

theorem Sel.castb {b b' : Wire} {k : Nat} {P' P : Program} (h : Sel b k P' P) (e : b=b') :
    Sel b' k P' P := e ▸ h

theorem selNotZero5 : ¬Placement5.zeroRegion 2400 := by
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega

theorem selShift_fix (j : Nat) (hj : j < 102) : shifted (Placement5.pi j) (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi_outside j 2400 hj selNotZero5]

theorem selShift0_fix : shifted Placement5.pi0 (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi0_outside 2400 selNotZero5]

theorem selSig_2400 : OB5.sig 511 (base 2400)=base 2400 := by
  rw [OB5.sig_base 511 2400 (le_refl _),if_neg (by omega)]

theorem selEndpoint_fix : HalfFieldOB5.endpointMap (base 2400)=base 2400 := by
  have hb : HalfFieldOB5.bank 2400=2400 := by decide
  have hp : Placement5.pi 51 2400=2400 := Placement5.pi_outside 51 2400 (by omega) selNotZero5
  have h1 : base 2400≠base 1796 := by decide
  have h2 : base 2400≠base 1285 := by decide
  show OB5.sig 511 ((Equiv.swap (base 1796) (base 1285))
    ((shifted (Placement5.pi 51)) ((shifted HalfFieldOB5.bank) (base 2400))))=base 2400
  rw [shifted_base,hb,shifted_base,hp,Equiv.swap_apply_of_ne_of_ne h1 h2,selSig_2400]

theorem selHost_fix : HostOB5.hostSwap (base 2400)=base 2400 := by
  have a1 : base 2400≠base 2409 := by decide
  have a2 : base 2400≠base 511 := by decide
  have a3 : base 2400≠base 2410 := by decide
  have a4 : base 2400≠base 1542 := by decide
  unfold HostOB5.hostSwap
  rw [if_neg a1,if_neg a2,if_neg a3,if_neg a4]

/-! ### Label 2400 is never used outside the windows -/

theorem selX511_away : base 2400∉wires [Instr.X (base 511)] := by
  intro h
  have e : base 2400=base 511 := by simpa [wires,Instr.wires] using h
  have := base_injective e
  omega

def selW0 : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset ∪ {base 2410}

theorem selW0_away : base 2400∉selW0 := by
  intro h
  simp only [selW0,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_map,
    Finset.mem_singleton] at h
  rcases h with (e|⟨j,hj,e⟩)|e
  · have := base_injective e; omega
  · have := base_injective e; have := Q6EndpointCell.ids_bound j hj; omega
  · have := base_injective e; omega

theorem selBody_away (divide : Bool) :
    base 2400∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := fun h =>
  selW0_away (Q6EndpointCell.body_support divide base (base 2409) (base 2410) selW0
    Finset.subset_union_left (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h)

theorem selHalf_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.half divide base (base 2409)) :=
  fun h => selW0_away (Q6EndpointCell.half_support divide base (base 2409) selW0
    Finset.subset_union_left h)

theorem selHalfE_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.halfE divide base (base 2409)) :=
  fun h => selHalf_away divide (Q6EndpointCell.halfE_wires divide _ _ h)

theorem selSwap_away : base 2400∉wires swapBody := by
 have sub : wires swapBody⊆wires (Q6EndpointCell.body true base (base 2409) (base 2409)) := by
  simp only [swapBody,Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y]
  exact Finset.subset_union_right
 have flag : base 2409∈selW0 := by simp [selW0]
 exact fun h => selW0_away (Q6EndpointCell.body_support true base (base 2409) (base 2409)
   selW0 Finset.subset_union_left flag (sub h))

theorem selSwapM_away : base 2400∉wires swapBodyM := by
  rw [swapBodyM,UncompSwap.mswap_wires]
  exact selSwap_away

theorem selHist_away (start : Nat) (hs : start+5 ≤ 512) :
    base 2400∉wires (History5.encode base start) ∧ base 2400∉wires (History5.decode base start) := by
  have lift (P : Program) (he : P=History5.encode base start ∨ P=History5.decode base start) :
      base 2400∉wires P := by
    intro hq
    obtain ⟨u,hu⟩ := History5.history_gate_mem base start P he _ hq
    have bound := History5.historyId_bound start hs u
    have hu' : base 2400=base (History5.historyId start u) := hu
    have := base_injective hu'
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem selCenter_away : base 2400∉wires HalfFieldOB5.centerT ∧
    base 2400∉wires HalfFieldOB5.canonT ∧ base 2400∉wires HalfFieldOB5.copyN := by
  have ids (q : Wire) (hq : q∈(HalfField.ids.map base).toFinset) : q≠base 2400 := by
    intro e
    subst e
    obtain ⟨i,hi,e⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have := base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    omega
  have ren (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base 2400∉wires (renameProgram HalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    rw [← selEndpoint_fix] at e
    exact ids q (hP hq) (HalfFieldOB5.endpointMap.injective e)
  exact ⟨ren _ HalfField.centerT_sites,ren _ HalfField.canonT_sites,
    fun h => ids _ (HalfField.copyN_sites h) rfl⟩

theorem selInt_away : base 2400∉wires (stackForwardT) ∧ base 2400∉wires (stackReverseT) := by
  have bad : base 2400∉OB5.integerSites := by
    intro h
    obtain ⟨l,e,hl⟩ := (OB5.integerSites_mem _).mp h
    have := base_injective e
    omega
  exact ⟨fun h => bad (StackOB5.forward_support (stackForwardT_subset h)),fun h => bad (StackOB5.reverse_support (stackReverseT_subset h))⟩

theorem selPrefix_away : base 2400∉(NativeFirstDirect.prefixSites base).toFinset := by
  intro h
  simp only [NativeFirstDirect.prefixSites,wireBlock,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  omega

theorem selClear_away : base 2400∉wires (skywalkArithmeticClear base) := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  simp [base]

/-! ### Letters -/

theorem selLetter_nodup (i : Nat) (hi : i < 510) :
    [base 2400,(tapeLetter i).1.1,base 2409].Nodup ∧ [base 2400,(tapeLetter i).1.2,base 2409].Nodup := by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i (by omega)]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,
    not_or,not_false_eq_true,base_injective.eq_iff]
  omega

theorem selLetters_nodup (j : Nat) (hj : j < 102) (l : MixedTranscriptLetter)
    (hl : l∈Replay5.letters j) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range.mp hk
  exact selLetter_nodup (5*j+k) (by omega)

theorem selRest_nodup (l : MixedTranscriptLetter) (hl : l∈Replay5.restLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range'_1.mp hk
  exact selLetter_nodup k (by omega)

/-! ### Cells and packets -/

theorem selCell_sel (divide : Bool) (g sw : Wire) (ig is : Bool)
 (hg : [base 2400,g,base 2409].Nodup) (hs : [base 2400,sw,base 2409].Nodup) :
 Sel (base 2400) 2 (cellS divide g sw)
   (OneFlagCell.cell divide base (base 2400) g sw (base 2409) ig is) := by
 have swap := ((Sel.refl _ _ selSwap_away).window sw (base 2409) is hs)
 have half (d : Bool) := ((Sel.refl _ _ (selHalf_away d)).window g (base 2409) ig hg)
 cases divide
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_false] using
     (swap.append (half false)).cast (by norm_num) rfl rfl
 · simpa only [cellS,OneFlagCell.cell,OneFlagCell.halfWindow,OneFlagCell.selectSwap,
     swapBody,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,if_true] using
     ((half true).append swap).cast (by norm_num) rfl rfl

theorem selRaw_sel (divide : Bool) (ls : List MixedTranscriptLetter)
    (hl : ∀ l∈ls, [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2409].Nodup) :
    Sel (base 2400) (2*ls.length) (rawReplayS divide ls) (OneFlagReplay.rawReplay divide ls) := by
  induction ls with
  | nil => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | cons l ls ih =>
    have hh := hl l (List.mem_cons_self ..)
    have rest := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    cases divide
    · exact (rest.append (selCell_sel false l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2)).cast
        (by simp only [List.length_cons]; omega) rfl rfl
    · exact ((selCell_sel true l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2).append rest).cast
        (by simp only [List.length_cons]; omega) rfl rfl

theorem selPacket_sel (divide : Bool) (j : Nat) (hj : j < 102) :
    Sel (base 2400) 10 (packetS divide j) (OneFlagReplay.packet divide j) := by
  have codec := selHist_away (5*j) (by omega)
  have r := selRaw_sel divide (Replay5.letters j) (selLetters_nodup j hj)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at r
  have b : Sel (base 2400) 10 (basePacketS divide j) (OneFlagReplay.basePacket divide j) :=
    (((Sel.refl _ _ codec.2).append r).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi j)) (selShift_fix j hj)

theorem selGroups_sel (divide : Bool) (j n : Nat) (bound : j+n ≤ 102) :
    Sel (base 2400) (10*n) (groupsS divide j n) (OneFlagReplay.groups divide j n) := by
  unfold groupsS OneFlagReplay.groups
  induction n generalizing j with
  | zero => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | succ n ih =>
    have head := selPacket_sel divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide
    · simp only [PacketSequence.program,Bool.false_eq_true,if_false]
      exact (rest.append head).cast (by ring) rfl rfl
    · simp only [PacketSequence.program,if_true]
      exact (head.append rest).cast (by ring) rfl rfl

theorem selFirstSwap_sel : Sel (base 2400) 1 firstSwapS OneFlagReplay.firstSwap := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwap_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstSwapM_sel : Sel (base 2400) 1 firstSwapMS OneFlagReplay.firstSwapM := by
  have n : [base 2400,base 1028,base 2409].Nodup := by decide
  exact ((Sel.refl _ _ selSwapM_away).window (base 1028) (base 2409)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstPacket_sel (divide : Bool) :
    Sel (base 2400) 9 (firstPacketS divide) (OneFlagReplay.firstPacket divide) := by
  have codec := selHist_away 0 (by omega)
  have r := selRaw_sel divide Replay5.restLetters selRest_nodup
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at r
  have body : Sel (base 2400) 9 (firstBodyS divide) (OneFlagReplay.firstBody divide) := by
    cases divide
    · exact (r.append selFirstSwapM_sel).cast (by norm_num) rfl rfl
    · exact (selFirstSwap_sel.append r).cast (by norm_num) rfl rfl
  have b : Sel (base 2400) 9 (baseFirstPacketS divide) (OneFlagReplay.baseFirstPacket divide) :=
    (((Sel.refl _ _ codec.2).append body).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi 0)) (selShift_fix 0 (by omega))

theorem selEnd_sel (divide : Bool) :
    Sel (base 2400) 1 (endPacketS divide) (OneFlagReplay.endPacket divide) := by
  have n : [base 2400,base 510,base 2409].Nodup := by decide
  have b : Sel (base 2400) 1 (rawEndS divide) (OneFlagReplay.rawEnd divide) :=
    ((Sel.refl _ _ (selHalfE_away divide)).window (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 n).cast (by norm_num) rfl rfl
  exact b.rename (shifted Placement5.pi0) selShift0_fix

/-! ### Replay, segment, kernel -/

theorem selLogical_sel (divide : Bool) :
    Sel (base 2400) 1020 (logicalReplayS divide) (OneFlagReplay.logicalReplay divide) := by
  have g := selGroups_sel divide 1 101 (by omega)
  have e := selEnd_sel divide
  have f := selFirstPacket_sel divide
  cases divide
  · exact ((e.append g).append f).cast (by norm_num) rfl rfl
  · exact ((f.append g).append e).cast (by norm_num) rfl rfl

theorem selReplay_sel (divide : Bool) :
    Sel (base 2400) 1020 (replayS divide) (OneFlagReplay.replay divide) :=
  ((selLogical_sel divide).rename_inj (OB5.sig 511) (OB5.sig_injective 511 (by decide))).castb
    selSig_2400

end ECDSAAdd.Entrant.OneFlagSW


-- ONEFLAG COMPONENT EntryRawOneFlag.lean
namespace ECDSAAdd.Entrant.OneFlagProviderSupport
open Arithmetic
 theorem replay_support (d : Bool) : wires (OneFlagReplay.replay d)⊆OB5Support.segSites := by
  exact (OneFlagReplay.replay_subset_old d).trans (Q6EndpointReplaySupport.replay_support d)
end ECDSAAdd.Entrant.OneFlagProviderSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI EntryFuse
attribute [local irreducible] run wires

def field5 : Program := OneFlagReplay.replay true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5 : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5 ++ [.X (base 511)])
def kernel5 : Program := NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
  hostField5 ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem field_support : wires field5⊆OB5Support.segSites := by
  simp only [field5,wires_append,Finset.union_subset_iff]
  exact ⟨OneFlagProviderSupport.replay_support true,HalfFieldOB5Support.copy_support,OwnQ5Endpoint.support.2⟩

theorem field_free : base 511∉wires field5 ∧ base 1542∉wires field5 :=
  ⟨fun h=>OB5Support.seg_host_free.1 (field_support h),fun h=>OB5Support.seg_host_free.2 (field_support h)⟩

theorem field5_unhosted_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run field5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (SegmentOB5.program true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) := by
    exact (regValue_congr _ _ _ paired.2.2).trans value
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hpPool : base 2409∉skywalkPoolWires base := by
    intro bad
    exact ho _ (by simp) (arith_block_subset_shared base 0 1798 (by omega) bad)
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have centerEq := center5_compare hn hpPool origin.basis facts.env legal facts.targetHigh
    facts.sourceHigh facts.sourceZero Y a3 v3 placedInput paired.1 paired.2.1 target
    ((List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4).take
      (measurementCount OwnQ5Endpoint.centerT))
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have oldReplacement:=Q6EndpointSegment.program_state_eq true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 (dummy++m4) placedInput
  have newReplacement:=OneFlagSegment.program_state_eq true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 (dummy++m4) placedInput
  have replacement := newReplacement.trans oldReplacement
  change run (SegmentOB5.program true) (dummy++m4) a3=v4
  rw [←replacement]
  have shape : OneFlagSegment.program true=OwnQ5Endpoint.centerT++field5 := by
    simp only [OneFlagSegment.program,field5,if_true]
  change run (OneFlagSegment.program true) (dummy++m4) a3=v4
  rw [shape,run_append]
  have drop : (dummy++m4).drop (measurementCount OwnQ5Endpoint.centerT)=m4 := by simp [dummy]
  rw [drop,centerEq]
  exact h4

theorem kernel5_field_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (KernelOB5.segH true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  let oldRecords := dummy++m4
  let v4' := run field5 m4 v3
  have unEq := field5_unhosted_state hn hlo ho x Y hx0 hx s t m1 m2 m3 m4 hg0 hs0 hf hin
    phase same value v1 v2 v3 v4' h1 h2 h3 rfl
  change run (SegmentOB5.program true) oldRecords a3=v4' at unEq
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have fresh := SegmentOB5.program_spec true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 oldRecords placedInput
  have inS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 placedInput
  have outS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero _ _ fresh.2
  have hostBits := encoded_host_bits5 x hx0 hx origin t3 a3 facts.trace encEq e3
  have in2409 : a3.basis (base 2409)=false := inS.1
  have in2410 : a3.basis (base 2410)=false := inS.2
  have in511 : a3.basis (base 511)=true := hostBits.1
  have in1542 : a3.basis (base 1542)=false := hostBits.2
  have out2409 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2409)=false := outS.1
  have out2410 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2410)=false := outS.2
  have away (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 := by
    intro mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have e := base_injective eq
    omega
  have inT (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
    (paired.2.1 _ (away i hi)).symm
  have freeP := KernelOB5.seg_free true
  have freeQ511 : base 511∉wires field5 := field_free.1
  have freeQ1542 : base 1542∉wires field5 := field_free.2
  have hosted := hosted_pair5 (SegmentOB5.program true) field5 a3 v3 oldRecords m4
    freeP.1 freeP.2 freeQ511 freeQ1542 in2409 in511 in2410 in1542
    ((inT 2409 (by omega)).trans in2409) ((inT 511 (by omega)).trans in511)
    ((inT 2410 (by omega)).trans in2410) ((inT 1542 (by omega)).trans in1542)
    out2409 out2410 unEq
  change run (KernelOB5.segH true) oldRecords a3=v4
  rw [show KernelOB5.segH true=[.X (base 511)]++
    (renameProgram HostOB5.hostSwap (SegmentOB5.program true)++[.X (base 511)]) from rfl,hosted]
  simpa only [hostField5] using h4

theorem kernel5_states
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 v5 v6 v7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4)
    (h5 : run (skywalkArithmeticClear base) m5 v4=v5)
    (h6 : run (stackReverseT) m6 v5=v6)
    (h7 : run (NativeFirstKnown.inverse base) m7 v6=v7) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s v7 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have old4 := kernel5_field_state hn hlo ho hf x Y hx0 hx s t m1 m2 m3 m4 hin hg0 hs0
    phase same value v1 v2 v3 v4 h1 h2 h3 h4
  exact KernelOB5.program_states true hn hlo ho hf x Y hx0 hx s
    m1 m2 m3 (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) m5 m6 m7
    hin hg0 hs0 a1 a2 a3 v4 v5 v6 v7 rfl rfl rfl old4 h5 h6 h7

theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  let P : State → State → Prop := fun initial out =>
    initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) hostField5 (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hp hs hv
      exact kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 hp hs hv v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 h4 h5 h6 h7) t m
  simpa only [kernel5,List.append_assoc] using all phase same value

end ECDSAAdd.Entrant.OneFlagEntryRaw


-- ONEFLAG COMPONENT SelectedOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] run wires kernel5
def field5S : Program := OneFlagSW.replayS true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def kernel5S : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostField5S ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem selField5 : SW.Sel (base 2400) 1020 field5S field5 := by
  have r:=OneFlagSW.selReplay_sel true
  have old:=Q5FusionFields.selField5
  have canonAway : base 2400∉wires OwnQ5Endpoint.canonT := by
    intro h
    exact old.away (by simp only [Q5FusionFields.field5S,wires_append,Finset.mem_union];exact Or.inr (Or.inr h))
  have cp:=SW.Sel.refl (base 2400) HalfFieldOB5.copyN SW.selCenter_away.2.2
  have cn:=SW.Sel.refl (base 2400) OwnQ5Endpoint.canonT canonAway
  simpa only [field5S,field5,Nat.add_zero] using r.append (cp.append cn)

theorem selHostField5 : SW.Sel (base 2400) 1020 hostField5S hostField5 := by
  have r := (selField5.rename_inj HostOB5.hostSwap HostOB5.hostSwap_injective).castb SW.selHost_fix
  have h := (SW.Sel.refl _ _ SW.selX511_away).append
    (r.append (SW.Sel.refl _ _ SW.selX511_away))
  simpa only [hostField5S,hostField5,Nat.zero_add,Nat.add_zero] using h

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 := by
  have native := NativeFirstDirect.prefix_support base
  have known := NativeFirstKnown.inverse_support base
  have fw : base 2400∉wires (NativeFirstDirect.forward base) := fun h => SW.selPrefix_away (native.1 h)
  have iv : base 2400∉wires (NativeFirstKnown.inverse base) := fun h => SW.selPrefix_away (known h)
  have ints := SW.selInt_away
  have h := ((((((SW.Sel.refl _ _ fw).append (SW.Sel.refl _ _ ints.1)).append
    (SW.Sel.refl _ _ SW.selClear_away)).append selHostField5).append
    (SW.Sel.refl _ _ SW.selClear_away)).append (SW.Sel.refl _ _ ints.2)).append (SW.Sel.refl _ _ iv)
  simpa only [kernel5S,kernel5,Nat.zero_add,Nat.add_zero] using h


attribute [local irreducible] kernel5S
def forceControl5 (s : State) : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩

theorem forceControl5_keep (s : State) (q : Wire) (hq : q≠base 2400) :
    (forceControl5 s).basis q=s.basis q := by simp [forceControl5,writeBit,Function.update_of_ne hq]

theorem forceControl5_true (s : State) : (forceControl5 s).basis (base 2400)=true := by
  simp [forceControl5,writeBit]

/-- The shortened selector-free division receives a half-centered numerator. -/
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := forceControl5 s
  let b := forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := forceControl5_true s
  have bb : b.basis (base 2400)=true := forceControl5_true t
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [forceControl5_true,forceControl5_true]
    · rw [forceControl5_keep t q e,forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong := kernel5_correct hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half
  obtain ⟨equiv,_⟩ := selKernel5.eq m b bb
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab,←equiv] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree := pool_run_agrees kernel5S (wires kernel5S) (Finset.Subset.refl _) m t b rfl
    (fun q hq => (forceControl5_keep t q (fun e => selKernel5.away (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run kernel5S m t).basis q=(run kernel5S m b).basis q := by
    by_cases used : q∈wires kernel5S
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e => numAway (e ▸ hq))
  · intro q hq
    by_cases e : q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ selKernel5.away).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (forceControl5_keep s q e))


end ECDSAAdd.Entrant.OneFlagEntryRaw


-- ONEFLAG COMPONENT EntrySupportOneFlag.lean
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OneFlagEntrySupport
open Arithmetic MappedCompressed OneFlagEntryRaw
attribute [local irreducible] wires
 theorem field_subset : wires field5⊆wires Q6EndpointEntryRaw.field5 := by
  simp only [field5,Q6EndpointEntryRaw.field5,wires_append]
  exact Finset.union_subset_union (OneFlagReplay.replay_subset_old true) (Finset.Subset.refl _)
 theorem host_subset : wires hostField5⊆wires Q6EndpointEntryRaw.hostField5 := by
  have h:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ field_subset
  simp only [hostField5,Q6EndpointEntryRaw.hostField5,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
 theorem hostS_subset : wires hostField5S⊆wires Q6EndpointEntryRaw.hostField5 :=
  selHostField5.sub.wires_sub.trans host_subset
 theorem host1542_free : base 1542∉wires hostField5 := by
  intro used
  apply OneFlagSegment.hosted1542_free true
  have sub : wires field5⊆wires (OneFlagSegment.program true) := by
   simp only [field5,OneFlagSegment.program,if_true,wires_append]
   exact Finset.subset_union_right
  have h:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ sub
  have full : wires hostField5⊆wires (OneFlagSegment.segH true) := by
   simp only [hostField5,OneFlagSegment.segH,wires_append]
   exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
  exact full used
 theorem hostS1542_free : base 1542∉wires hostField5S := fun h=>host1542_free (selHostField5.sub.wires_sub h)
end ECDSAAdd.Entrant.OneFlagEntrySupport


-- ONEFLAG COMPONENT PhaseKernelsOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryQ5
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5
  OneFlagEntryRaw Q5Global718
attribute [local irreducible] run wires OneFlagEntryRaw.kernel5 OneFlagEntryRaw.kernel5S

def kernel5 : Program:=Q5FusionPhase.relocated hostField5
def kernel5S : Program:=Q5FusionPhase.relocated hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free : base 1026∉wires hostField5 := by
 exact fun used=>EndpointEntryQ5.hostField5_free (OneFlagEntrySupport.host_subset used)
theorem hostField5S_free : base 1026∉wires hostField5S := by
 exact fun used=>EndpointEntryQ5.hostField5_free (OneFlagEntrySupport.hostS_subset used)
theorem old_shape : Q5FusionPhase.kernel hostField5=OneFlagEntryRaw.kernel5 := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,OneFlagEntryRaw.kernel5,List.append_assoc]
theorem old_shapeS : Q5FusionPhase.kernel hostField5S=OneFlagEntryRaw.kernel5S := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,OneFlagEntryRaw.kernel5S,List.append_assoc]
theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old := OneFlagEntryRaw.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have contract : DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5) m t) := by
    simpa only [old_shape] using old
  have eq := Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5 true
    hin same hostField5_free contract
  rw [kernel5,eq]
  exact contract

theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old := OneFlagEntryRaw.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q5FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shapeS] using old.2.2
  have eq := Q5FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S
    hin same hostField5S_free frame
  simp only [kernel5S,eq,old_shapeS]
  exact old


end ECDSAAdd.Entrant.OneFlagEntryQ5


-- ONEFLAG COMPONENT KernelsQ6OneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 OneFlagEntryRaw
attribute [local irreducible] run wires

def kernel5 : Program:=Q6FusionPhase.relocated OneFlagEntryRaw.hostField5
def kernel5S : Program:=Q6FusionPhase.relocated OneFlagEntryRaw.hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free1541 : base 1541∉wires OneFlagEntryRaw.hostField5 := by
 exact fun used=>OwnEndpointEntryQ6.hostField5_free1541 (OneFlagEntrySupport.host_subset used)
theorem hostField5S_free1541 : base 1541∉wires OneFlagEntryRaw.hostField5S := by
 exact fun used=>OwnEndpointEntryQ6.hostField5_free1541 (OneFlagEntrySupport.hostS_subset used)

theorem outer_shape (F : Program) : Q6FusionPhase.kernel F=Q5FusionPhase.relocated F := by
 simp only [Q6FusionPhase.kernel,Q5FusionPhase.relocated,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase]
theorem old_shape_kernel5 : Q6FusionPhase.kernel OneFlagEntryRaw.hostField5=OneFlagEntryQ5.kernel5 := by
 simpa only [OneFlagEntryQ5.kernel5] using outer_shape OneFlagEntryRaw.hostField5
theorem old_shape_kernel5S : Q6FusionPhase.kernel OneFlagEntryRaw.hostField5S=OneFlagEntryQ5.kernel5S := by
 simpa only [OneFlagEntryQ5.kernel5S] using outer_shape OneFlagEntryRaw.hostField5S
theorem kernel5_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=OneFlagEntryQ5.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel OneFlagEntryRaw.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m OneFlagEntryRaw.hostField5 hin same hostField5_free1541 frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
theorem kernel5S_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=OneFlagEntryQ5.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel OneFlagEntryRaw.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m OneFlagEntryRaw.hostField5S hin same hostField5S_free1541 frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old

end ECDSAAdd.Entrant.OneFlagEntryQ6


-- ONEFLAG COMPONENT KernelsQ7OneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 OneFlagEntryRaw
attribute [local irreducible] run wires

def kernel5 : Program:=Q7FusionPhase.relocated OneFlagEntryRaw.hostField5
def kernel5S : Program:=Q7FusionPhase.relocated OneFlagEntryRaw.hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free1542 : base 1542∉wires OneFlagEntryRaw.hostField5 := OneFlagEntrySupport.host1542_free
theorem hostField5S_free1542 : base 1542∉wires OneFlagEntryRaw.hostField5S := OneFlagEntrySupport.hostS1542_free

theorem outer_shape (F : Program) : Q7FusionPhase.kernel F=Q6FusionPhase.relocated F := Q7FusionPhase.old_shape F
theorem old_shape_kernel5 : Q7FusionPhase.kernel OneFlagEntryRaw.hostField5=OneFlagEntryQ6.kernel5 := by
 simpa only [OneFlagEntryQ6.kernel5] using outer_shape OneFlagEntryRaw.hostField5
theorem old_shape_kernel5S : Q7FusionPhase.kernel OneFlagEntryRaw.hostField5S=OneFlagEntryQ6.kernel5S := by
 simpa only [OneFlagEntryQ6.kernel5S] using outer_shape OneFlagEntryRaw.hostField5S
theorem kernel5_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=OneFlagEntryQ6.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel OneFlagEntryRaw.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m OneFlagEntryRaw.hostField5 hin same hostField5_free1542 frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
theorem kernel5S_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=OneFlagEntryQ6.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q7FusionPhase.kernel OneFlagEntryRaw.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m OneFlagEntryRaw.hostField5S hin same hostField5S_free1542 frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old

end ECDSAAdd.Entrant.OwnOneFlagEntryQ7


-- ONEFLAG COMPONENT GeometryQ6OneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryGeometry
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires run
set_option maxHeartbeats 1000000 in
theorem host_support (P : Program) (hp:wires P⊆OB5Support.segSites) : wires ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)]))⊆OB5Support.logicalSites := by
  have mem (i : Nat) (hi : i ∈ OB5Support.logicalIndices) : base i ∈ OB5Support.logicalSites :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have m511 : base 511 ∈ OB5Support.logicalSites := mem 511 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have m1542 : base 1542 ∈ OB5Support.logicalSites := mem 1542 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have x (r : Wire) (hr : r ∈ wires [Instr.X (base 511)]) : r = base 511 := by
    simpa [wires, Instr.wires] using hr
  intro q hq
  simp only [wires_append, Finset.mem_union] at hq
  rcases hq with h|h|h
  · rw [x q h]; exact m511
  · rw [renameProgram_support] at h
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp h
    have hs := hp hold
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    unfold HostOB5.hostSwap
    split_ifs with c d e f
    · exact m511
    · exfalso
      have := base_injective d
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · exact m1542
    · exfalso
      have := base_injective f
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · apply mem
      have c' : i ≠ 2409 := fun h => c (by rw [h])
      have e' : i ≠ 2410 := fun h => e (by rw [h])
      simp only [OB5Support.segIndices, OB5Support.logicalIndices, List.mem_append, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
  · rw [x q h]; exact m511

theorem raw_support : wires OneFlagEntryRaw.kernel5⊆OB5Support.logicalSites := by
 have first:=(NativeFirstDirect.prefix_support base).1.trans OB5Support.prefixSites_sub_logical
 have f:=stackForwardT_subset.trans (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
 have c:=OB5Support.clear_support_logical
 have b:=host_support OneFlagEntryRaw.field5 OneFlagEntryRaw.field_support
 have r:=stackReverseT_subset.trans (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
 have last:=(NativeFirstKnown.inverse_support base).trans OB5Support.prefixSites_sub_logical
 simp only [OneFlagEntryRaw.kernel5,wires_append,Finset.union_subset_iff,and_assoc]
 exact ⟨first,f,c,b,c,r,last⟩

theorem q5support (F : Program) (old:wires (Q5FusionPhase.kernel F)⊆OB5Support.logicalSites) :
 wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites := by
 simp only [Q5FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
 simp only [Q5FusionPhase.relocated,wires_append,Finset.union_subset_iff]
 exact ⟨OwnQ5Integer.rename_support _ old.1,old.2.1,OwnQ5Integer.rename_support _ old.2.2⟩
theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=719∨i=1541) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1541
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 719 (Or.inl rfl)
  · by_cases b:q=base 719
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1541 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)

theorem q6support (F : Program) (old : wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←OneFlagEntryQ6.outer_shape] at old
  simp only [Q6FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q6FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩

theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q6FusionPhase.relocated G) (Q6FusionPhase.relocated F) := by
  have fp : base 2400∉wires q5First := by
    simpa only [q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires q5Last := by
    simpa only [q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q6FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh

end ECDSAAdd.Entrant.OneFlagEntryGeometry
namespace ECDSAAdd.Entrant.OneFlagEntryQ6
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires

theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
 apply OneFlagEntryGeometry.q6support
 apply OneFlagEntryGeometry.q5support
 simpa only [OneFlagEntryQ5.old_shape] using OneFlagEntryGeometry.raw_support

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 :=
 OneFlagEntryGeometry.sel _ _ OneFlagEntryRaw.selHostField5

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 selKernel5.sub.wires_sub.trans kernel5_support
end ECDSAAdd.Entrant.OneFlagEntryQ6


-- ONEFLAG COMPONENT GeometryQ7OneFlag.lean
namespace ECDSAAdd.Entrant.OneFlagEntryGeometryQ7
open Arithmetic MappedCompressed Q7IntegerHost
attribute [local irreducible] wires
 theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=720∨i=1542) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1542
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 720 (Or.inl rfl)
  · by_cases b:q=base 720
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1542 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq
 theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)
 theorem support (F : Program) (old : wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q7FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←Q7FusionPhase.old_shape] at old
  simp only [Q7FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q7FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩
 theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q7FusionPhase.relocated G) (Q7FusionPhase.relocated F) := by
  have fix6 : Q6IntegerHost.swap (base 2400)=base 2400 := by decide +kernel
  have fp : base 2400∉wires Q7FusionPhase.q6First := by
    unfold Q7FusionPhase.q6First
    apply OwnPlusHost.rename_avoid _ _ _ fix6
    simpa only [Q6IntegerHost.q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires Q7FusionPhase.q6Last := by
    unfold Q7FusionPhase.q6Last
    apply OwnPlusHost.rename_avoid _ _ _ fix6
    simpa only [Q6IntegerHost.q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q7FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh
end ECDSAAdd.Entrant.OneFlagEntryGeometryQ7
namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic MappedCompressed
attribute [local irreducible] wires
 theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
  apply OneFlagEntryGeometryQ7.support
  exact OneFlagEntryQ6.kernel5_support
 theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 :=
  OneFlagEntryGeometryQ7.sel _ _ OneFlagEntryRaw.selHostField5
 theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
  selKernel5.sub.wires_sub.trans kernel5_support
end ECDSAAdd.Entrant.OwnOneFlagEntryQ7


-- ONEFLAG COMPONENT CallersOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section
namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem q7part19_mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- A renamed replay receives the same pool as a canonical virtual state,
while its actual numerator has already been half-centered. -/
theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires OwnOneFlagEntryQ7.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f OwnOneFlagEntryQ7.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [q7part19_mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [q7part19_mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [q7part19_mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := OwnOneFlagEntryQ7.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective OwnOneFlagEntryQ7.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (q7part19_mapped_regS f _ (run OwnOneFlagEntryQ7.kernel5S m b).basis
      (run (renameProgram f OwnOneFlagEntryQ7.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain OwnOneFlagEntryQ7.kernel5S sites m t q image).trans (same q hq)


end ECDSAAdd.Entrant.OwnOneFlagEntryQ7
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires toffoliCount measurementCount
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) OwnOneFlagEntryQ7.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ kernel5S_support

private theorem q7part19_divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem q7part19_numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem q7part19_control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    q7part19_divisor_sitesS q7part19_numerator_sitesS q7part19_control_siteS (OwnOneFlagEntryQ7.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

end ECDSAAdd.Entrant.OwnOneFlagEntryQ7
end


namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] run arithEntryS arithS fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep
end ECDSAAdd.Entrant.OwnOneFlagEntryQ7


-- ONEFLAG COMPONENT ResourcesOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryResources
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] wires run toffoliCount measurementCount

theorem field_sub : InstrSub OneFlagEntryRaw.field5 (OneFlagSegment.program true) := by
 constructor
 · intro i hi
   left
   change i∈OwnQ5Endpoint.centerT++OneFlagEntryRaw.field5
   exact List.mem_append_right _ hi
 · change Challenge.gateSlots OneFlagEntryRaw.field5≤
     Challenge.gateSlots (OwnQ5Endpoint.centerT++OneFlagEntryRaw.field5)
   rw [Challenge.gateSlots_append]
   omega

theorem raw_physical : GatePhysical OneFlagEntryRaw.kernel5 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have f:=field_sub.physical (OneFlagSegment.physical true cfg.1 cfg.2.1 cfg.2.2)
 have hosted:=Q5FusionFields.host_physical OneFlagEntryRaw.field5 f
 have first:=(NativeFirstDirect.programs_physical base base_pool_nodup).1
 have last:=NativeFirstKnown.inverse_physical base base_pool_nodup
 simp only [OneFlagEntryRaw.kernel5,gatePhysical_append]
 exact ⟨⟨⟨⟨⟨⟨first,stackForwardT_physical⟩,mappedClear_physical⟩,hosted⟩,
   mappedClear_physical⟩,stackReverseT_physical⟩,last⟩

theorem raw_slots : Challenge.gateSlots OneFlagEntryRaw.kernel5≤20500006 := by
 have native:=Baselines.nativeFirst_gateSlots_le base
 have integer:=Stack5.slots_le base base_pool_nodup 1 511 (by omega)
 have f:=StackOB5.forward_counts.2.2
 have r:=StackOB5.reverse_counts.2.2
 have ft:=stackForwardT_metrics.2.2
 have rt:=stackReverseT_metrics.2.2
 have field:=field_sub.slots.trans (OneFlagSegment.gateSlots_le true)
 have clear:Challenge.gateSlots (skywalkArithmeticClear base)=3:=by
   simp [skywalkArithmeticClear,skywalkTerminalClear,Challenge.gateSlots,Challenge.instructionSlots]
 have x:Challenge.gateSlots [.X (base 511)]=1:=rfl
 simp only [OneFlagEntryRaw.kernel5,OneFlagEntryRaw.hostField5,
   Challenge.gateSlots_append,Baselines.rename_gateSlots,clear,x]
 omega

/-- Exact counts use the new field body and protected integer budget, not a mutable old parent. -/
theorem raw_counts : toffoliCount OneFlagEntryRaw.kernel5=1048904 ∧
 measurementCount OneFlagEntryRaw.kernel5=720767 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have r:=OneFlagReplay.replay_counts_eq true cfg.1 (cfg.2.1 _ (by simp))
 have fields : toffoliCount OneFlagEntryRaw.field5=toffoliCount Q6EndpointEntryRaw.field5 ∧
     measurementCount OneFlagEntryRaw.field5=measurementCount Q6EndpointEntryRaw.field5 := by
  simp only [OneFlagEntryRaw.field5,Q6EndpointEntryRaw.field5,toffoliCount_append,measurementCount_append]
  exact ⟨congrArg (fun n=>n+_) r.1,congrArg (fun n=>n+_) r.2⟩
 have ren:=renameProgram_counts HostOB5.hostSwap OneFlagEntryRaw.field5
 have renOld:=renameProgram_counts HostOB5.hostSwap Q6EndpointEntryRaw.field5
 have prior:=EndpointEntryResources.raw_counts
 simp only [OneFlagEntryRaw.kernel5,OneFlagEntryRaw.hostField5,
   Q6EndpointEntryRaw.kernel5,Q6EndpointEntryRaw.hostField5,
   toffoliCount_append,measurementCount_append,ren.1,ren.2,renOld.1,renOld.2] at prior ⊢
 constructor <;> omega

theorem q5_physical (F : Program) (h:GatePhysical (Q5FusionPhase.kernel F)) :
 GatePhysical (Q5FusionPhase.relocated F) := by
 simp only [Q5FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q5FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.2.2⟩

theorem q6_physical (F : Program) (h:GatePhysical (Q5FusionPhase.relocated F)) :
 GatePhysical (Q6FusionPhase.relocated F) := by
 rw [←OneFlagEntryQ6.outer_shape] at h
 simp only [Q6FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q6FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.2.2⟩

theorem q7_physical (F : Program) (h:GatePhysical (Q6FusionPhase.relocated F)) :
 GatePhysical (Q7FusionPhase.relocated F) := by
 rw [←Q7FusionPhase.old_shape] at h
 simp only [Q7FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q7FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q7IntegerHost.swap Q7IntegerHost.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q7IntegerHost.swap Q7IntegerHost.swap.injective _ h.2.2⟩

theorem outer_slots (F : Program) :
 Challenge.gateSlots (Q7FusionPhase.relocated F)=Challenge.gateSlots (Q5FusionPhase.kernel F) := by
 simp only [Q7FusionPhase.relocated,Q7FusionPhase.q6First,Q7FusionPhase.q6Last,
   Q5FusionPhase.kernel,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase,
   Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem outer_counts (F : Program) :
 toffoliCount (Q7FusionPhase.relocated F)=toffoliCount (Q5FusionPhase.kernel F) ∧
 measurementCount (Q7FusionPhase.relocated F)=measurementCount (Q5FusionPhase.kernel F) := by
 have a:=Q7FusionPhase.relocated_counts F
 rw [Q7FusionPhase.old_shape] at a
 have b:=Q6FusionPhase.relocated_counts F
 rw [OneFlagEntryQ6.outer_shape] at b
 have c:=Q5FusionPhase.relocated_counts F
 exact ⟨a.1.trans (b.1.trans c.1),a.2.trans (b.2.trans c.2)⟩
end ECDSAAdd.Entrant.OneFlagEntryResources

namespace ECDSAAdd.Entrant.OwnOneFlagEntryQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk OneFlagEntryRaw
attribute [local irreducible] run wires toffoliCount measurementCount

theorem kernel5_physical : GatePhysical kernel5 := by
 apply OneFlagEntryResources.q7_physical
 apply OneFlagEntryResources.q6_physical
 apply OneFlagEntryResources.q5_physical
 simpa only [OneFlagEntryQ5.old_shape] using OneFlagEntryResources.raw_physical

theorem kernel5S_physical : GatePhysical kernel5S := selKernel5.sub.physical kernel5_physical

theorem kernel5_slots_le : Challenge.gateSlots kernel5≤20500006 := by
 rw [kernel5,OneFlagEntryResources.outer_slots,OneFlagEntryQ5.old_shape]
 exact OneFlagEntryResources.raw_slots

theorem kernel5S_slots_le : Challenge.gateSlots kernel5S≤20500006 :=
 selKernel5.sub.slots.trans kernel5_slots_le

theorem kernel5_counts : toffoliCount kernel5=1048904 ∧ measurementCount kernel5=720767 := by
 have h:=OneFlagEntryResources.outer_counts OneFlagEntryRaw.hostField5
 rw [OneFlagEntryQ5.old_shape] at h
 simpa only [kernel5,h.1,h.2] using OneFlagEntryResources.raw_counts

theorem kernel5S_counts : toffoliCount kernel5S=1047884 ∧ measurementCount kernel5S=720767 := by
 have c:=kernel5_counts
 have t:=selKernel5.tc
 have m:=selKernel5.mc
 constructor <;> omega

theorem arithEntryS_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 GatePhysical (arithEntryS L) := by
 apply gatePhysical_rename_support (wireFn2 L) kernel5S
 · intro a ha b hb eq
   exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernel5S_support ha))
     b (ArithmeticOB5.logical_sub_old (kernel5S_support hb)) eq
 · exact kernel5S_physical

theorem arithEntryS_counts (L : ControlledPointLayout) :
 toffoliCount (arithEntryS L)=1047884 ∧ measurementCount (arithEntryS L)=720767 := by
 simpa only [arithEntryS,(renameProgram_counts (wireFn2 L) kernel5S).1,
   (renameProgram_counts (wireFn2 L) kernel5S).2] using kernel5S_counts

theorem arithEntryS_gateSlots_le (L : ControlledPointLayout) :
 Challenge.gateSlots (arithEntryS L)≤20500006 := by
 simpa only [arithEntryS,Baselines.rename_gateSlots] using kernel5S_slots_le

theorem fusedDivisionF_counts (L : ControlledPointLayout) (hw:L.Widths) (k:Fp) :
 toffoliCount (fusedDivisionF L k)=1048650 ∧ measurementCount (fusedDivisionF L k)=721534 := by
 have a:=EntryFuse.fusedY_counts L hw k
 have b:=arithEntryS_counts L
 simp only [fusedDivisionF,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
 constructor <;> trivial
end ECDSAAdd.Entrant.OwnOneFlagEntryQ7


-- ONEFLAG COMPONENT OmissionsOneFlag.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagEntryOmissions
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 CompressedPointDialog
attribute [local irreducible] wires
private theorem q7part21_placed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i k : Nat)
 (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
 (free : base i∉wires P) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) P) := by
 rw [renameProgram_support]
 intro h
 obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
 have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
 have back := (placement2 L hw hn).injectiveOnSlots old
   (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
 exact free (back ▸ used)
private theorem q7part21_logical (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 omega
private theorem q7part21_entry_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnEntryFuseQ5.kernel5S := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact OwnEntryFuseQ5.kernel5S_1026_free

private theorem q7part21_q5_free (i : Nat) (hi : i∈[2312,766,765,767,1026]) :
 base i∉wires (Q5FusionPhase.relocated OneFlagEntryRaw.hostField5S) := by
 have h:=q7part21_entry_old i hi
 have newField : base i∉wires OneFlagEntryRaw.hostField5S := by
  intro used
  have oldField : base i∉wires Q6EndpointEntryRaw.hostField5 := by
   apply Q6EndpointOmissions.host_free _ i
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega
   · apply Q6EndpointOmissions.field_free
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; omega
  exact oldField (OneFlagEntrySupport.hostS_subset used)
 simp only [OwnEntryFuseQ5.kernel5S,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] at h ⊢
 exact ⟨h.1,newField,h.2.2⟩

private theorem q7part21_kernel_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∉wires OneFlagEntryQ6.kernel5S := by
 by_cases last : i=1541
 · subst i
   simpa only [OneFlagEntryQ6.kernel5S] using
    Q6FusionPhase.relocated_1541_free _ OneFlagEntryQ6.hostField5S_free1541
 · have prior : i∈[2312,766,765,767,1026] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
   have old:=q7part21_q5_free i prior
   rw [←OneFlagEntryQ6.outer_shape] at old
   simp only [Q6FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q6IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq; exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
      omega
   have first:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.1
   have final:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.2.2
   simpa only [OneFlagEntryQ6.kernel5S,Q6FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
     And.intro first (And.intro old.2.1 final)

theorem kernel_free7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires OwnOneFlagEntryQ7.kernel5S := by
 by_cases last : i=1542
 · subst i
   simpa only [OwnOneFlagEntryQ7.kernel5S] using
    Q7FusionPhase.relocated_1542_free _ OneFlagEntrySupport.hostS1542_free
 · have prior : i∈[2312,766,765,767,1026,1541] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto
   have old:=q7part21_kernel_free i prior
   change base i∉wires (Q6FusionPhase.relocated OneFlagEntryRaw.hostField5S) at old
   rw [←Q7FusionPhase.old_shape] at old
   simp only [Q7FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q7IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq;exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior;omega
   change base i∉wires (Q7FusionPhase.relocated OneFlagEntryRaw.hostField5S)
   simp only [Q7FusionPhase.relocated,wires_append,Finset.mem_union,not_or]
   exact ⟨OwnPlusHost.rename_avoid _ _ _ fix old.1,old.2.1,OwnPlusHost.rename_avoid _ _ _ fix old.2.2⟩
private theorem q7part21_logical7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
 theorem entry_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
 L.core.poolWire k∉wires (OwnOneFlagEntryQ7.arithEntryS L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 2312 1800
     (q7part21_logical7 2312 (by simp)) (by rfl) (kernel_free7 2312 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 766 766
     (q7part21_logical7 766 (by simp)) (by rfl) (kernel_free7 766 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 765 765
     (q7part21_logical7 765 (by simp)) (by rfl) (kernel_free7 765 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 767 767
     (q7part21_logical7 767 (by simp)) (by rfl) (kernel_free7 767 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 1026 770
     (q7part21_logical7 1026 (by simp)) (by rfl) (kernel_free7 1026 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 1541 1285
     (q7part21_logical7 1541 (by simp)) (by rfl) (kernel_free7 1541 (by simp))
 · exact q7part21_placed L hw hn OwnOneFlagEntryQ7.kernel5S OwnOneFlagEntryQ7.kernel5S_support 1542 1286
     (q7part21_logical7 1542 (by simp)) (by rfl) (kernel_free7 1542 (by simp))
end ECDSAAdd.Entrant.OneFlagEntryOmissions


-- ONEFLAG COMPONENT EntryPropertiesOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.OneFlagEntryProperties
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount
theorem division_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (OwnOneFlagEntryQ7.fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [OwnOneFlagEntryQ7.fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    OwnOneFlagEntryQ7.arithEntryS_support L hw⟩

theorem division_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (OwnOneFlagEntryQ7.fusedDivisionF L k) := by
  simp only [OwnOneFlagEntryQ7.fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,OwnOneFlagEntryQ7.arithEntryS_physical L hw hn⟩

theorem division_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285,1286]) (c : Fp) :
    L.core.poolWire k∉wires (OwnOneFlagEntryQ7.fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [OwnOneFlagEntryQ7.fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),OneFlagEntryOmissions.entry_avoids L hw hn k hk⟩


theorem division_slots (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 gateSlots (OwnOneFlagEntryQ7.fusedDivisionF L k)≤20525006 := by
 have d:=OwnOneFlagEntryQ7.arithEntryS_gateSlots_le L
 have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
 simp only [OwnOneFlagEntryQ7.fusedDivisionF,EntryFuse.fusedY,gateSlots_append]
 omega

theorem division_counts_diff (Dold : Program)
 (oldCounts : toffoliCount Dold=1048904 ∧ measurementCount Dold=721534)
 (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF L k)+254=toffoliCount Dold ∧
 measurementCount (OwnOneFlagEntryQ7.fusedDivisionF L k)=measurementCount Dold := by
 have a:=OwnOneFlagEntryQ7.fusedDivisionF_counts L hw k
 constructor <;> omega
end ECDSAAdd.Entrant.OneFlagEntryProperties


-- ONEFLAG COMPONENT CumulativePhaseOneFlag.lean
namespace ECDSAAdd.Entrant.OneFlagPhase
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed
attribute [local irreducible] run wires
 theorem state_eq_of_frame (hn : (skywalkSharedWires base).Nodup)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (a b : State) (m : List Bool) (F : Program)
    (input : SkywalkArithmeticInput base x Y.val a.basis) (same : Q5FusionPhase.Paired a b)
    (free5 : base 1026∉wires F) (free6 : base 1541∉wires F) (free7 : base 1542∉wires F)
    (frame : ∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel F) m b).basis q=a.basis q) :
    run (Q7FusionPhase.relocated F) m b=run (Q5FusionPhase.kernel F) m b := by
  have eq5:=Q5FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F input same free5 frame
  have shape6 : Q6FusionPhase.kernel F=Q5FusionPhase.relocated F := by
   simp only [Q6FusionPhase.kernel,Q5FusionPhase.relocated,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
     Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase]
  have frame6 : ∀q,q∉wireBlock base 2056 256 → (run (Q6FusionPhase.kernel F) m b).basis q=a.basis q := by
   simpa only [shape6,eq5] using frame
  have eq6:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F input same free6 frame6
  have frame7 : ∀q,q∉wireBlock base 2056 256 → (run (Q7FusionPhase.kernel F) m b).basis q=a.basis q := by
   simpa only [Q7FusionPhase.old_shape,eq6,shape6,eq5] using frame
  have eq7:=Q7FusionPhase.state_eq_of_frame hn x Y hx0 hx a b m F input same free7 frame7
  exact eq7.trans (by simpa only [Q7FusionPhase.old_shape,shape6] using eq6.trans (by simpa only [shape6] using eq5))
end ECDSAAdd.Entrant.OneFlagPhase


-- ONEFLAG COMPONENT EndpointFalseEq.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitRaw
open Arithmetic
 theorem cell_eq (divide : Bool) (w : Nat→Wire) (b g sw sign eff : Wire) (ig is : Bool) :
  Q6EndpointCell.cell divide w b g sw sign eff ig is=OneBankCell5.cell divide w b g sw sign eff ig is := by rfl
 theorem endpoint_false_eq (w : Nat→Wire) (b g sign : Wire) (ig : Bool) :
  Q6EndpointCell.endpoint false w b g sign ig=OneBankCell5.endpoint false w b g sign ig := by rfl
 theorem rawReplay_false_eq (ls : List MixedTranscriptLetter) :
  Q6EndpointReplay.rawReplay false ls=OneBankReplay5.rawReplay false ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [Q6EndpointReplay.rawReplay,OneBankReplay5.rawReplay,Bool.false_eq_true,if_false,cell_eq,ih]
 theorem body_false_eq (j : Nat) : Q6EndpointReplay.body false j=OneBankReplay5.body false j := rawReplay_false_eq _
 theorem packet_false_eq (j : Nat) : Q6EndpointReplay.packet false j=OneBankReplay5.packet false j := by
  simp only [Q6EndpointReplay.packet,OneBankReplay5.packet,Q6EndpointReplay.basePacket,OneBankReplay5.basePacket,body_false_eq]
 theorem groups_false_eq (j n : Nat) : Q6EndpointReplay.groups false j n=OneBankReplay5.groups false j n := by
  have e : Q6EndpointReplay.packet false=OneBankReplay5.packet false := funext packet_false_eq
  simp only [Q6EndpointReplay.groups,OneBankReplay5.groups,e]
 theorem first_false_eq : Q6EndpointReplay.firstPacket false=OneBankReplay5.firstPacket false := by
  simp only [Q6EndpointReplay.firstPacket,OneBankReplay5.firstPacket,Q6EndpointReplay.baseFirstPacket,OneBankReplay5.baseFirstPacket,
   Q6EndpointReplay.firstBody,OneBankReplay5.firstBody,Bool.false_eq_true,if_false,rawReplay_false_eq]
 theorem end_false_eq : Q6EndpointReplay.endPacket false=OneBankReplay5.endPacket false := by
  simp only [Q6EndpointReplay.endPacket,OneBankReplay5.endPacket,Q6EndpointReplay.rawEnd,OneBankReplay5.rawEnd,endpoint_false_eq]
 theorem replay_false_eq : Q6EndpointReplay.replay false=OneBankReplay5.replay false := by
  simp only [Q6EndpointReplay.replay,OneBankReplay5.replay,Q6EndpointReplay.logicalReplay,OneBankReplay5.logicalReplay,
   Bool.false_eq_true,if_false,end_false_eq,groups_false_eq,first_false_eq]
 theorem endpoint_false_program_eq : Q6EndpointSegment.program false=SegmentOB5.program false := by
  simp only [Q6EndpointSegment.program,SegmentOB5.program,Bool.false_eq_true,if_false,replay_false_eq]
end ECDSAAdd.Entrant.OneFlagExitRaw


-- ONEFLAG COMPONENT ExitRawOneFlag.lean
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.MappedCompressed
  ECDSAAdd.Entrant ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitRaw
open BalancedField History5 DirectSkywalk CompressedFieldSupport CompressedAllocation OffsetBorrowedCanonical
attribute [local irreducible] run wires History5.allEncode

theorem encoded_field_value (origin : BasisState) (X Y : Fp) (s : State)
    (frame : EncodedFieldFrame5 base (base 2409) origin X Y s) :
    regValue (wireBlock base 2056 256) s.basis=centerWord X := by
  obtain ⟨raw,phase,pair,encoded⟩ := frame
  have rEq := balancedSharedPorts_r base (base 2409)
  rw [rEq] at pair
  apply (regValue_congr _ _ _ ?_).trans pair.1
  intro q hq
  rw [encoded]
  apply run_preserves_outside
  intro used
  exact EntryFuse.pool_away q (List.mem_toFinset.mp (HalfField5.encoder_pool_support used)) hq

/-- A centered output and its canonicalized frame agree on every other wire. -/
theorem field_canonical_pair_logical (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (H : Fp) (a b : State)
    (half : EncodedFieldFrame5 base (base 2409) origin H 0 a)
    (canon : EncodedCanonicalFrame5 origin (2*H) 0 b)
    (phase : a.phase=b.phase) :
    ∀q,q∉wireBlock base 2056 256 → a.basis q=b.basis q := by
  let w : State := ⟨a.phase,fun q => if q∈wireBlock base 2056 256 then a.basis q else b.basis q⟩
  have value : regValue (wireBlock base 2056 256) w.basis=centerWord H := by
    apply (regValue_congr _ _ _ ?_).trans (encoded_field_value origin H 0 a half)
    intro q hq
    simp only [w,if_pos hq]
  have same : ∀q,q∉wireBlock base 2056 256 → w.basis q=b.basis q := by
    intro q hq
    simp only [w,if_neg hq]
  have two : (2:Fp)≠0 := by decide
  have div : 2*H/2=H := by field_simp
  have framed := EntryFuse.encoded_retarget5 hn origin hr hy (2*H) b w phase same
    (by simpa only [div] using value) canon
  rw [div] at framed
  have eq := EntryFuse.encoded_field_unique5 origin H 0 a w half framed rfl
  intro q hq
  exact (congrFun (congrArg State.basis eq) q).trans (same q hq)

theorem field_canonical_pair (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (H : Fp) (a b : State)
    (half : FieldFrameOB5.EncodedFieldFrame origin H 0 a)
    (canon : FieldFrameOB5.EncodedCanonicalFrame origin (2*H) 0 b)
    (phase : a.phase=b.phase) :
    regValue (wireBlock base 2056 256) a.basis=centerWord H ∧
    ∀q,q∉wireBlock base 2056 256 → a.basis q=b.basis q := by
  have same := field_canonical_pair_logical hn origin hr hy H
    (pullState (OB5.sig 511) a) (pullState (OB5.sig 511) b) half canon phase
  have value := encoded_field_value origin H 0 (pullState (OB5.sig 511) a) half
  constructor
  · apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    change a.basis q=a.basis (OB5.sig 511 q)
    rw [EntryFuse.sig_num_fix q hq]
  · intro q hq
    have h := same (OB5.sig 511 q) (EntryFuse.sig_num_away q hq)
    change a.basis (OB5.sig 511 (OB5.sig 511 q))=b.basis (OB5.sig 511 (OB5.sig 511 q)) at h
    simpa only [OB5.sig_invol 511 (by decide)] using h

def fieldMul : Program := OwnQ5Endpoint.centerT ++
  (HalfFieldOB5.copyN ++ OneFlagReplay.replay false)
attribute [local irreducible] fieldMul OneFlagReplay.replay OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT

theorem full_field_shape : OneFlagSegment.program false=fieldMul++OwnQ5Endpoint.canonT := by
  simp only [OneFlagSegment.program,fieldMul,Bool.false_eq_true,if_false,List.append_assoc]

theorem fieldMul_frame
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let H := if origin (base 2400) then Y/2*(x:Fp) else Y/2
    (run fieldMul m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin H 0 (run fieldMul m s) := by
  let c := run OwnQ5Endpoint.centerT (m.take (measurementCount OwnQ5Endpoint.centerT)) s
  let rest := m.drop (measurementCount OwnQ5Endpoint.centerT)
  let d := run HalfFieldOB5.copyN (rest.take (measurementCount HalfFieldOB5.copyN)) c
  have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y s
    (m.take (measurementCount OwnQ5Endpoint.centerT)) input
  have c2 := HalfFieldOB5.copy_fill hn origin (Y/2) c
    (rest.take (measurementCount HalfFieldOB5.copyN)) c1.2
  let ctx : OneFlagReplay.Context origin := ⟨hn,ho,hp,hf,hg0,hs0,env,legal,hr⟩
  have c3 := OneFlagReplay.inverse_frame origin ctx x hx0 hx trace (Y/2) d
    (rest.drop (measurementCount HalfFieldOB5.copyN)) c2.2
  exact ⟨by simpa only [fieldMul,run_append,c,d,rest] using c3.1.trans (c2.1.trans c1.1),
    by simpa only [fieldMul,run_append,c,d,rest] using c3.2⟩

theorem fieldMul_pair
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let a := run fieldMul m s
    let b := run (SegmentOB5.program false) m s
    let H := if origin (base 2400) then Y/2*(x:Fp) else Y/2
    a.phase=b.phase ∧ regValue (wireBlock base 2056 256) a.basis=centerWord H ∧
      ∀q,q∉wireBlock base 2056 256 → a.basis q=b.basis q := by
  have half := fieldMul_frame hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have canon := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _
    (run fieldMul m s) (m.drop (measurementCount fieldMul)) half.2
  have same := (OneFlagSegment.program_state_eq false hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input).trans
    (Q6EndpointSegment.program_state_eq false hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input)
  have shape : run (SegmentOB5.program false) m s=
      run OwnQ5Endpoint.canonT (m.drop (measurementCount fieldMul)) (run fieldMul m s) := by
    rw [←same,full_field_shape,run_append,run_take]
  rw [←shape] at canon
  exact ⟨canon.1.symm,field_canonical_pair hn origin hr hy _ _ _ half.2 canon.2 canon.1.symm⟩

def hostMul : Program := [.X (base 511)] ++
  (renameProgram HostOB5.hostSwap fieldMul ++ [.X (base 511)])
attribute [local irreducible] hostMul

theorem fieldMul_wires_subset : wires fieldMul⊆wires (SegmentOB5.program false) := by
  have newSub : wires fieldMul⊆wires (OneFlagSegment.program false) := by
    rw [full_field_shape,wires_append]
    exact Finset.subset_union_left
  have oldSub:=OneFlagSegment.subset_old false
  rw [endpoint_false_program_eq] at oldSub
  exact newSub.trans oldSub

theorem hostMul_wires_subset : wires hostMul⊆wires (KernelOB5.segH false) := by
  have sub:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ fieldMul_wires_subset
  simp only [hostMul,KernelOB5.segH,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union sub (Finset.Subset.refl _))

theorem hostMul_free : base 1026∉wires hostMul := fun used =>
  OwnQ5Actual.hosted_field_free false (hostMul_wires_subset used)

theorem hostMul_pair
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s)
    (in511 : s.basis (base 511)=true) (in1542 : s.basis (base 1542)=false) :
    let a := run hostMul m s
    let b := run (KernelOB5.segH false) m s
    let H := if origin (base 2400) then Y/2*(x:Fp) else Y/2
    a.phase=b.phase ∧ regValue (wireBlock base 2056 256) a.basis=centerWord H ∧
      ∀q,q∉wireBlock base 2056 256 → a.basis q=b.basis q := by
  have pair := fieldMul_pair hn ho hp hf origin hg0 hs0 env legal hr hy ha x hx0 hx trace Y s m input
  have old := SegmentOB5.program_spec false hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have ins := EntryFuse.encoded_selectors5 hn hp origin hg0 hs0 ha Y s input
  have outs := EntryFuse.encoded_selectors5 hn hp origin hg0 hs0 ha _ _ old.2
  have away (i : Nat) (hi : i=2409 ∨ i=2410) : base i∉wireBlock base 2056 256 :=
    OwnPlusHost.not_block i 2056 256 (by rcases hi with rfl|rfl <;> omega)
  have qg : (run fieldMul m s).basis (base 2409)=false :=
    (pair.2.2 _ (away 2409 (Or.inl rfl))).trans outs.1
  have qs : (run fieldMul m s).basis (base 2410)=false :=
    (pair.2.2 _ (away 2410 (Or.inr rfl))).trans outs.2
  have oldfree := KernelOB5.seg_free false
  have short := HostOB5.hosted_run fieldMul s m
    (fun h => oldfree.1 (fieldMul_wires_subset h))
    (fun h => oldfree.2 (fieldMul_wires_subset h)) ins.1 in511 ins.2 in1542 qg qs
  have full := HostOB5.hosted_run (SegmentOB5.program false) s m
    oldfree.1 oldfree.2 ins.1 in511 ins.2 in1542 outs.1 outs.2
  simpa only [hostMul,KernelOB5.segH,short,full] using pair

theorem clear_pool : wires (skywalkArithmeticClear base)⊆(skywalkPoolWires base).toFinset := EntryFuse.clear_pool5

theorem reverse_pool : wires stackReverseT⊆(skywalkPoolWires base).toFinset := by
  apply stackReverseT_subset.trans
  apply StackOB5.reverse_support.trans
  intro q hq
  obtain ⟨i,rfl,hi⟩ := (OB5.integerSites_mem q).mp hq
  exact List.mem_toFinset.mpr (arith_mem base 0 1798 i (by omega) (by omega))

theorem native_inverse_pool : wires (NativeFirstKnown.inverse base)⊆(skywalkPoolWires base).toFinset := by
  apply (NativeFirstKnown.inverse_support base).trans
  intro q hq
  exact List.mem_toFinset.mpr (NativeFirstDirect.prefix_pool_subset base (List.mem_toFinset.mp hq))

def rawKernel : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostMul ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base
attribute [local irreducible] rawKernel NativeFirstDirect.forward NativeFirstKnown.inverse
  stackForwardT stackReverseT skywalkArithmeticClear compactForward5

theorem rawKernel_states
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 s=s1)
    (h2 : run stackForwardT m2 s1=s2)
    (h3 : run (skywalkArithmeticClear base) m3 s2=s3)
    (h4 : run hostMul m4 s3=s4)
    (h5 : run (skywalkArithmeticClear base) m5 s4=s5)
    (h6 : run stackReverseT m6 s5=s6)
    (h7 : run (NativeFirstKnown.inverse base) m7 s6=s7) :
    s7.phase=s.phase ∧
      regValue (wireBlock base 2056 256) s7.basis=
        centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → s7.basis q=s.basis q := by
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 input
  rw [h1] at first
  have firstW := (W.compactSkywalkStage_one base _ s1.basis).mpr first
  let t2 := run (compactForward5 base 1 511) m2 s1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 s1=t2 :=
    Stack5.forward_old_eq base (skywalkShared_integer_nodup base hn) hlo x p hp0 hx0 hpo hpp
      gap hx cop s1 m2 m2 first
  have e2 : s2=pullState (OB5.sig 511) t2 := by
    rw [←h2,stackForwardT_run hn hlo x hx0 hx s1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx s1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : s3=pullState (OB5.sig 511) t3 := by
    rw [←h3,e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 input s1 t2 t3 h1 rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have placed : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 s3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) s3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have bits := EntryFuse.encoded_host_bits5 x hx0 hx origin t3 s3 facts.trace encEq e3
  have pair := hostMul_pair hn ho hp hf origin.basis hg hs facts.env legal facts.targetHigh
    facts.sourceHigh facts.sourceZero x hx0 hx facts.trace Y s3 m4 placed bits.1 bits.2
  rw [h4] at pair
  let v4 := run (KernelOB5.segH false) m4 s3
  let v5 := run (skywalkArithmeticClear base) m5 v4
  let v6 := run stackReverseT m6 v5
  let v7 := run (NativeFirstKnown.inverse base) m7 v6
  have old := KernelOB5.program_states false hn hlo ho hf x Y hx0 hx s m1 m2 m3 m4 m5 m6 m7
    input hg0 hs0 s1 s2 s3 v4 v5 v6 v7 h1 h2 h3 rfl rfl rfl rfl
  have after := EntryFuse.pool_three (skywalkArithmeticClear base) stackReverseT
    (NativeFirstKnown.inverse base) clear_pool reverse_pool native_inverse_pool s4 v4 m5 m6 m7
    pair.1 pair.2.2 v5 v6 v7 rfl rfl rfl
  change (run (NativeFirstKnown.inverse base) m7
      (run stackReverseT m6 (run (skywalkArithmeticClear base) m5 s4))).phase=v7.phase ∧
    (∀q,q∉wireBlock base 2056 256 →
      (run (NativeFirstKnown.inverse base) m7
        (run stackReverseT m6 (run (skywalkArithmeticClear base) m5 s4))).basis q=v7.basis q) ∧ _ at after
  rw [h5,h6,h7] at after
  have keeps (q : Wire) (hq : q∈wireBlock base 2056 256) : s7.basis q=s4.basis q := by
    have away (P : Program) (hpP : wires P⊆(skywalkPoolWires base).toFinset) : q∉wires P :=
      fun used => EntryFuse.pool_away q (List.mem_toFinset.mp (hpP used)) hq
    rw [←h7,run_preserves_outside _ _ _ _ (away _ native_inverse_pool),
      ←h6,run_preserves_outside _ _ _ _ (away _ reverse_pool),
      ←h5,run_preserves_outside _ _ _ _ (away _ clear_pool)]
  have H : (if origin.basis (base 2400) then Y/2*(x:Fp) else Y/2)=
      directSkywalkResult false (s.basis (base 2400)) x Y/2 := by
    rw [facts.controls _ (by simp)]
    unfold directSkywalkResult skywalkArithmeticResult
    cases s.basis (base 2400) <;> simp only [Bool.false_eq_true,if_false,if_true]
    ring
  refine ⟨after.1.trans old.1,?_,fun q hq => (after.2.1 q hq).trans (old.2.2 q hq)⟩
  exact (regValue_congr _ _ _ keeps).trans (pair.2.1.trans (congrArg centerWord H))

theorem rawKernel_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run rawKernel m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput base x Y.val initial.basis → initial.basis (base 2409)=false →
    initial.basis (base 2410)=false →
    out.phase=initial.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (initial.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=initial.basis q
  have all := skywalkRunSeven (NativeFirstDirect.forward base) stackForwardT
    (skywalkArithmeticClear base) hostMul (skywalkArithmeticClear base) stackReverseT
    (NativeFirstKnown.inverse base) P (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hin hg hs
      exact rawKernel_states hn hlo ho hf x Y hx0 hx initial m1 m2 m3 m4 m5 m6 m7 hin hg hs
        s1 s2 s3 s4 s5 s6 s7 h1 h2 h3 h4 h5 h6 h7) s m
  simpa only [rawKernel,List.append_assoc] using all input hg0 hs0


end ECDSAAdd.Entrant.OneFlagExitRaw


-- ONEFLAG COMPONENT SelectedExitRawOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 CompressedFieldSupport
attribute [local irreducible] run wires rawKernel

def fieldMulS : Program := OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ OneFlagSW.replayS false)
def hostMulS : Program := [.X (base 511)] ++
  (renameProgram HostOB5.hostSwap fieldMulS ++ [.X (base 511)])
def rawKernelS : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostMulS ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base
attribute [local irreducible] fieldMulS hostMulS

theorem selField : SW.Sel (base 2400) 1020 fieldMulS fieldMul := by
  have centerSub : LaneI.InstrSub OwnQ5Endpoint.centerT (SW.segmentS false) := by
    constructor
    · intro i hi
      left
      simp only [SW.segmentS,Bool.false_eq_true,if_false,List.mem_append]
      exact Or.inl hi
    · simp only [SW.segmentS,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
      omega
  have away : base 2400∉wires OwnQ5Endpoint.centerT := fun h =>
    (SW.selSegment_sel false).away (centerSub.wires_sub h)
  have h := (SW.Sel.refl _ _ away).append
    ((SW.Sel.refl _ _ SW.selCenter_away.2.2).append (OneFlagSW.selReplay_sel false))
  simpa only [fieldMulS,fieldMul,Nat.zero_add] using h

theorem selHost : SW.Sel (base 2400) 1020 hostMulS hostMul := by
  have r := (selField.rename_inj HostOB5.hostSwap HostOB5.hostSwap_injective).castb SW.selHost_fix
  have h := (SW.Sel.refl _ _ SW.selX511_away).append
    (r.append (SW.Sel.refl _ _ SW.selX511_away))
  simpa only [hostMulS,hostMul,Nat.zero_add,Nat.add_zero] using h

theorem selRawKernel : SW.Sel (base 2400) 1020 rawKernelS rawKernel := by
  have native := NativeFirstDirect.prefix_support base
  have known := NativeFirstKnown.inverse_support base
  have fw : base 2400∉wires (NativeFirstDirect.forward base) := fun h => SW.selPrefix_away (native.1 h)
  have iv : base 2400∉wires (NativeFirstKnown.inverse base) := fun h => SW.selPrefix_away (known h)
  have ints := SW.selInt_away
  have h := ((((((SW.Sel.refl _ _ fw).append (SW.Sel.refl _ _ ints.1)).append
    (SW.Sel.refl _ _ SW.selClear_away)).append selHost).append
    (SW.Sel.refl _ _ SW.selClear_away)).append (SW.Sel.refl _ _ ints.2)).append (SW.Sel.refl _ _ iv)
  simpa only [rawKernelS,rawKernel,Nat.zero_add,Nat.add_zero] using h
attribute [local irreducible] rawKernelS

open SW
theorem rawKernelS_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    (run rawKernelS m s).phase=s.phase ∧
    regValue (skywalkArithmeticNumerator base) (run rawKernelS m s).basis=
      centerWord (Y*(x:Fp)/2) ∧
    ∀ q,q∉skywalkArithmeticNumerator base → (run rawKernelS m s).basis q=s.basis q := by
  have sel := selRawKernel
  let t : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩
  have tq (q : Wire) (hq : q≠base 2400) : t.basis q=s.basis q := by
    simp only [t,writeBit,Function.update_of_ne hq]
  have tb : t.basis (base 2400)=true := by simp only [t,writeBit,Function.update_self]
  have bShared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have bDiv : base 2400∉skywalkArithmeticDivisor base := fun h =>
    bShared (arith_block_subset_shared base 770 256 (by omega) h)
  have bNum : base 2400∉skywalkArithmeticNumerator base := fun h =>
    bShared (arith_block_subset_shared base 2056 256 (by omega) h)
  have tin : SkywalkArithmeticInput base x Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · rw [←hin.1]
      exact regValue_congr _ _ _ (fun q hq => tq q (fun e => bDiv (e ▸ hq)))
    · rw [←hin.2.1]
      exact regValue_congr _ _ _ (fun q hq => tq q (fun e => bNum (e ▸ hq)))
    · intro q hq hdx hdy
      rw [tq q (fun e => bShared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have tg : t.basis (base 2409)=false := (tq _ (by simp [base])).trans hg0
  have ts : t.basis (base 2410)=false := (tq _ (by simp [base])).trans hs0
  have spec := rawKernel_correct hn hlo ho hf x Y hx0 hx t m tin tg ts
  obtain ⟨eq,_⟩ := sel.eq m t tb
  rw [tb,←eq] at spec
  have agree := pool_run_agrees rawKernelS (wires rawKernelS)
    (Finset.Subset.refl _) m s t rfl (fun w hw => (tq w (fun e => sel.away (e ▸ hw))).symm)
  have same (q : Wire) (hq : q≠base 2400) :
      (run rawKernelS m s).basis q=(run rawKernelS m t).basis q := by
    by_cases hw : q∈wires rawKernelS
    · exact agree.2 q hw
    · rw [run_preserves_outside _ m s q hw,run_preserves_outside _ m t q hw,tq q hq]
  refine ⟨agree.1.trans spec.1,?_,?_⟩
  · have r := spec.2.1
    simp only [directSkywalkResult,skywalkArithmeticResult,Bool.false_eq_true,if_false,if_true] at r
    rw [←r]
    exact regValue_congr _ _ _ (fun q hq => same q (fun e => bNum (e ▸ hq)))
  · intro q hq
    by_cases hb : q=base 2400
    · subst hb
      exact run_preserves_outside _ m s _ sel.away
    · rw [same q hb,spec.2.2 q hq,tq q hb]

end ECDSAAdd.Entrant.OneFlagExitRaw


-- ONEFLAG COMPONENT ExitKernelsOneFlag.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitSupport
open Arithmetic MappedCompressed OneFlagExitRaw
attribute [local irreducible] wires
 theorem host1026_free : base 1026∉wires hostMul := hostMul_free
 theorem host1541_free : base 1541∉wires hostMul := fun h=>
  OwnQ6Actual.hosted_field_free false (hostMul_wires_subset h)
 theorem host1542_free : base 1542∉wires hostMul := by
  have sub : wires fieldMul⊆wires (OneFlagSegment.program false) := by
   rw [full_field_shape,wires_append]
   exact Finset.subset_union_left
  have h:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ sub
  have full : wires hostMul⊆wires (OneFlagSegment.segH false) := by
   simp only [hostMul,OneFlagSegment.segH,wires_append]
   exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
  exact fun used=>OneFlagSegment.hosted1542_free false (full used)
 theorem hostS1026_free : base 1026∉wires hostMulS := fun h=>host1026_free (selHost.sub.wires_sub h)
 theorem hostS1541_free : base 1541∉wires hostMulS := fun h=>host1541_free (selHost.sub.wires_sub h)
 theorem hostS1542_free : base 1542∉wires hostMulS := fun h=>host1542_free (selHost.sub.wires_sub h)
 theorem raw_shape : Q5FusionPhase.kernel hostMul=rawKernel := by
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,rawKernel,List.append_assoc]
 theorem raw_shapeS : Q5FusionPhase.kernel hostMulS=rawKernelS := by
  simp only [Q5FusionPhase.kernel,Q5Global718.firstPhase,Q5Global718.lastPhase,rawKernelS,List.append_assoc]
end ECDSAAdd.Entrant.OneFlagExitSupport
namespace ECDSAAdd.Entrant.OwnOneFlagExitQ7
open Arithmetic MappedCompressed Secp256k1 DirectSkywalk BalancedField History5 OneFlagExitRaw OneFlagExitSupport
attribute [local irreducible] run wires rawKernel rawKernelS
 def kernel : Program:=Q7FusionPhase.relocated hostMul
 def kernelS : Program:=Q7FusionPhase.relocated hostMulS
attribute [local irreducible] kernel kernelS
 theorem kernel_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run kernel m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=
      centerWord (directSkywalkResult false (s.basis (base 2400)) x Y/2) ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=rawKernel_correct hn hlo ho hf x Y hx0 hx s m input hg0 hs0
  have frame : ∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel hostMul) m s).basis q=s.basis q := by
   simpa only [raw_shape] using old.2.2
  have eq:=OneFlagPhase.state_eq_of_frame hn x Y hx0 hx s s m hostMul input (fun _ _=>rfl)
    host1026_free host1541_free host1542_free frame
  simpa only [kernel,eq,raw_shape] using old
 theorem kernelS_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false) :
    let out := run kernelS m s
    out.phase=s.phase ∧ regValue (skywalkArithmeticNumerator base) out.basis=centerWord (Y*(x:Fp)/2) ∧
      ∀q,q∉skywalkArithmeticNumerator base → out.basis q=s.basis q := by
  have old:=rawKernelS_correct hn hlo ho hf x Y hx0 hx s m input hg0 hs0
  have frame : ∀q,q∉wireBlock base 2056 256 → (run (Q5FusionPhase.kernel hostMulS) m s).basis q=s.basis q := by
   simpa only [raw_shapeS] using old.2.2
  have eq:=OneFlagPhase.state_eq_of_frame hn x Y hx0 hx s s m hostMulS input (fun _ _=>rfl)
    hostS1026_free hostS1541_free hostS1542_free frame
  simpa only [kernelS,eq,raw_shapeS] using old
end ECDSAAdd.Entrant.OwnOneFlagExitQ7


-- ONEFLAG COMPONENT ExitGeometryOneFlag.lean
namespace ECDSAAdd.Entrant.OneFlagExitGeometry
open Arithmetic MappedCompressed OneFlagExitRaw
attribute [local irreducible] wires
 theorem field_support : wires OneFlagExitRaw.fieldMul⊆OB5Support.segSites := by
  simp only [OneFlagExitRaw.fieldMul,wires_append,Finset.union_subset_iff]
  exact ⟨OwnQ5Endpoint.support.1,HalfFieldOB5Support.copy_support,OneFlagProviderSupport.replay_support false⟩
 theorem raw_support : wires rawKernel⊆OB5Support.logicalSites := by
  have first:=(NativeFirstDirect.prefix_support base).1.trans OB5Support.prefixSites_sub_logical
  have f:=stackForwardT_subset.trans (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
  have c:=OB5Support.clear_support_logical
  have b:=OneFlagEntryGeometry.host_support OneFlagExitRaw.fieldMul field_support
  have r:=stackReverseT_subset.trans (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
  have last:=(NativeFirstKnown.inverse_support base).trans OB5Support.prefixSites_sub_logical
  simp only [rawKernel,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨first,f,c,b,c,r,last⟩
end ECDSAAdd.Entrant.OneFlagExitGeometry
namespace ECDSAAdd.Entrant.OwnOneFlagExitQ7
open Arithmetic MappedCompressed OneFlagExitRaw
attribute [local irreducible] wires
 theorem kernel_support : wires kernel⊆OB5Support.logicalSites := by
  apply OneFlagEntryGeometryQ7.support
  apply OneFlagEntryGeometry.q6support
  apply OneFlagEntryGeometry.q5support
  simpa only [OneFlagExitSupport.raw_shape] using OneFlagExitGeometry.raw_support
 theorem selKernel : SW.Sel (base 2400) 1020 kernelS kernel :=
  OneFlagEntryGeometryQ7.sel _ _ OneFlagExitRaw.selHost
 theorem kernelS_support : wires kernelS⊆OB5Support.logicalSites :=
  selKernel.sub.wires_sub.trans kernel_support
end ECDSAAdd.Entrant.OwnOneFlagExitQ7


-- ONEFLAG COMPONENT ExitCallersOneFlag.lean
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnOneFlagExitQ7
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed CompressedAllocation CompressedFieldSupport
 OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] wires run
 def arithExit (L : ControlledPointLayout) : Program:=renameProgram (wireFn2 L) kernelS
theorem arithExit_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (hX : X < p) (hX0 : 0 < X) (hY : Y < p)
    (s : State) (m : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (arithExit L) m s).phase=s.phase ∧
    regValue L.point.y (run (arithExit L) m s).basis=
      centerWord (((Y:Fp)*(X:Fp))/2) ∧
    ∀q,q∉L.point.y → (run (arithExit L) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,
    selectorG,selectorS,zeroFlag⟩
  have dx : (wireBlock base 770 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have dy : (wireBlock base 2056 256).toFinset⊆OB5Support.logicalSites := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [wireBlock,List.mem_range'_1] at hi
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    omega
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have result := OwnExitFuseQ5.wordTransfer L (wireFn2 L) OB5Support.logicalSites
    (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
      (ArithmeticOB5.logical_sub_old hb) eq)
    divisorMap numeratorMap
    (fun q hq used hx hy => sharedWork q hq (ArithmeticOB5.logical_sub_old used) hx hy)
    selectorG selectorS dx dy X (Y:Fp) (centerWord (((Y:Fp)*(X:Fp))/2))
    s m hx (hy.trans yValue.symm) hc
    kernelS kernelS_support
    (fun t records input hg hs => kernelS_correct
      config.1 above config.2.1 config.2.2 X (Y:Fp) hX0 hX t records input hg hs)
  simpa only [arithExit] using result

end ECDSAAdd.Entrant.OwnOneFlagExitQ7


-- ONEFLAG COMPONENT ExitResourcesOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitResources
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
 CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] wires run toffoliCount measurementCount
 theorem field_sub : InstrSub OneFlagExitRaw.fieldMul (OneFlagSegment.program false) := by
  rw [OneFlagExitRaw.full_field_shape]
  constructor
  · intro i hi;left;exact List.mem_append_left _ hi
  · rw [Challenge.gateSlots_append];omega
 theorem raw_physical : GatePhysical OneFlagExitRaw.rawKernel := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have f:=field_sub.physical (OneFlagSegment.physical false cfg.1 cfg.2.1 cfg.2.2)
  have hosted:=Q5FusionFields.host_physical OneFlagExitRaw.fieldMul f
  have first:=(NativeFirstDirect.programs_physical base base_pool_nodup).1
  have last:=NativeFirstKnown.inverse_physical base base_pool_nodup
  simp only [OneFlagExitRaw.rawKernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,stackForwardT_physical⟩,mappedClear_physical⟩,hosted⟩,mappedClear_physical⟩,stackReverseT_physical⟩,last⟩
 theorem raw_slots : Challenge.gateSlots OneFlagExitRaw.rawKernel≤20500006 := by
  have native:=Baselines.nativeFirst_gateSlots_le base
  have integer:=Stack5.slots_le base base_pool_nodup 1 511 (by omega)
  have f:=StackOB5.forward_counts.2.2
  have r:=StackOB5.reverse_counts.2.2
  have ft:=stackForwardT_metrics.2.2
  have rt:=stackReverseT_metrics.2.2
  have field:=field_sub.slots.trans (OneFlagSegment.gateSlots_le false)
  have clear:Challenge.gateSlots (skywalkArithmeticClear base)=3:=by
   simp [skywalkArithmeticClear,skywalkTerminalClear,Challenge.gateSlots,Challenge.instructionSlots]
  have x:Challenge.gateSlots [.X (base 511)]=1:=rfl
  simp only [OneFlagExitRaw.rawKernel,OneFlagExitRaw.hostMul,Challenge.gateSlots_append,Baselines.rename_gateSlots,clear,x]
  omega
 theorem raw_counts : toffoliCount OneFlagExitRaw.rawKernel=1048902 ∧ measurementCount OneFlagExitRaw.rawKernel=721023 := by
  have cfg:=MappedCompressed.LaneA.laneLogical_config
  have r:=OneFlagReplay.replay_counts_eq false cfg.1 (cfg.2.1 _ (by simp))
  rw [OneFlagExitRaw.replay_false_eq] at r
  have fields : toffoliCount OneFlagExitRaw.fieldMul=toffoliCount OwnExitFuseQ5.fieldMul ∧
   measurementCount OneFlagExitRaw.fieldMul=measurementCount OwnExitFuseQ5.fieldMul := by
   simp only [OneFlagExitRaw.fieldMul,OwnExitFuseQ5.fieldMul,toffoliCount_append,measurementCount_append]
   constructor <;> omega
  have ren:=renameProgram_counts HostOB5.hostSwap OneFlagExitRaw.fieldMul
  have renOld:=renameProgram_counts HostOB5.hostSwap OwnExitFuseQ5.fieldMul
  have outer:=Q5FusionPhase.relocated_counts OwnExitFuseQ5.hostMul
  rw [OwnExitFuseQ5.raw_shape] at outer
  have prior:=OwnExitFuseQ5.kernel_counts
  simp only [OwnExitFuseQ5.kernel,outer.1,outer.2] at prior
  simp only [OneFlagExitRaw.rawKernel,OneFlagExitRaw.hostMul,OwnExitFuseQ5.rawKernel,OwnExitFuseQ5.hostMul,
   toffoliCount_append,measurementCount_append,ren.1,ren.2,renOld.1,renOld.2] at prior ⊢
  constructor <;> omega
end ECDSAAdd.Entrant.OneFlagExitResources
namespace ECDSAAdd.Entrant.OwnOneFlagExitQ7
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk OneFlagExitRaw
attribute [local irreducible] run wires toffoliCount measurementCount
 theorem kernel_physical : GatePhysical kernel := by
  apply OneFlagEntryResources.q7_physical
  apply OneFlagEntryResources.q6_physical
  apply OneFlagEntryResources.q5_physical
  simpa only [OneFlagExitSupport.raw_shape] using OneFlagExitResources.raw_physical
 theorem kernelS_physical : GatePhysical kernelS := selKernel.sub.physical kernel_physical
 theorem kernel_slots_le : Challenge.gateSlots kernel≤20500006 := by
  rw [kernel,OneFlagEntryResources.outer_slots,OneFlagExitSupport.raw_shape]
  exact OneFlagExitResources.raw_slots
 theorem kernelS_slots_le : Challenge.gateSlots kernelS≤20500006 := selKernel.sub.slots.trans kernel_slots_le
 theorem kernel_counts : toffoliCount kernel=1048902 ∧ measurementCount kernel=721023 := by
  have h:=OneFlagEntryResources.outer_counts OneFlagExitRaw.hostMul
  rw [OneFlagExitSupport.raw_shape] at h
  simpa only [kernel,h.1,h.2] using OneFlagExitResources.raw_counts
 theorem kernelS_counts : toffoliCount kernelS=1047882 ∧ measurementCount kernelS=721023 := by
  have c:=kernel_counts;have t:=selKernel.tc;have m:=selKernel.mc
  constructor <;> omega
 theorem arithExit_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) : GatePhysical (arithExit L) := by
  apply gatePhysical_rename_support (wireFn2 L) kernelS
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernelS_support ha))
     b (ArithmeticOB5.logical_sub_old (kernelS_support hb)) eq
  · exact kernelS_physical
 theorem arithExit_counts (L : ControlledPointLayout) : toffoliCount (arithExit L)=1047882 ∧ measurementCount (arithExit L)=721023 := by
  simpa only [arithExit,(renameProgram_counts (wireFn2 L) kernelS).1,(renameProgram_counts (wireFn2 L) kernelS).2] using kernelS_counts
 theorem arithExit_slots_le (L : ControlledPointLayout) : Challenge.gateSlots (arithExit L)≤20500006 := by
  simpa only [arithExit,Baselines.rename_gateSlots] using kernelS_slots_le
end ECDSAAdd.Entrant.OwnOneFlagExitQ7


-- ONEFLAG COMPONENT ExitOmissionsOneFlag.lean
namespace ECDSAAdd.Entrant.OneFlagExitOmissionBase
open Arithmetic MappedCompressed
attribute [local irreducible] wires
 theorem host_subset : wires OneFlagExitRaw.hostMul⊆wires OwnExitFuseQ5.hostMul := by
  have r:=OneFlagReplay.replay_subset_old false
  rw [OneFlagExitRaw.replay_false_eq] at r
  have field : wires OneFlagExitRaw.fieldMul⊆wires OwnExitFuseQ5.fieldMul := by
   simp only [OneFlagExitRaw.fieldMul,OwnExitFuseQ5.fieldMul,wires_append]
   exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) r)
  have h:=OneFlagReplay.rename_subset HostOB5.hostSwap _ _ field
  simp only [OneFlagExitRaw.hostMul,OwnExitFuseQ5.hostMul,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union h (Finset.Subset.refl _))
 theorem hostS_subset : wires OneFlagExitRaw.hostMulS⊆wires OwnExitFuseQ5.hostMul :=
  OneFlagExitRaw.selHost.sub.wires_sub.trans host_subset
end ECDSAAdd.Entrant.OneFlagExitOmissionBase
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagExitOmissions
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 CompressedPointDialog
attribute [local irreducible] wires
private theorem q7part31_placed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i k : Nat)
 (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
 (free : base i∉wires P) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) P) := by
 rw [renameProgram_support]
 intro h
 obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
 have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
 have back := (placement2 L hw hn).injectiveOnSlots old
   (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
 exact free (back ▸ used)
private theorem q7part31_logical (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 omega
private theorem q7part31_exit_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnExitFuseQ5.kernel := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free false) (OwnExitFuseQ5.kernel_sub.wires_sub used)
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub used)
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub used)
 · exact fun used => OwnQ5Integer.preserve_avoid false _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free false) (OwnExitFuseQ5.kernel_sub.wires_sub used)
 · exact OwnExitFuseQ5.kernel_1026_free

private theorem q7part31_q5_free (i : Nat) (hi : i∈[2312,766,765,767,1026]) :
 base i∉wires (Q5FusionPhase.relocated OneFlagExitRaw.hostMulS) := by
 have h:=q7part31_exit_old i hi
 have newField : base i∉wires OneFlagExitRaw.hostMulS := by
  have oldField : base i∉wires OwnExitFuseQ5.hostMul := by
   have h:=q7part31_exit_old i hi
   simp only [OwnExitFuseQ5.kernel,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] at h
   exact h.2.1
  exact fun used=>oldField (OneFlagExitOmissionBase.hostS_subset used)
 simp only [OwnExitFuseQ5.kernel,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] at h ⊢
 exact ⟨h.1,newField,h.2.2⟩

private theorem q7part31_kernel_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∉wires (Q6FusionPhase.relocated OneFlagExitRaw.hostMulS) := by
 by_cases last : i=1541
 · subst i
   exact Q6FusionPhase.relocated_1541_free _ OneFlagExitSupport.hostS1541_free
 · have prior : i∈[2312,766,765,767,1026] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
   have old:=q7part31_q5_free i prior
   rw [←OneFlagEntryQ6.outer_shape] at old
   simp only [Q6FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q6IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq; exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
      omega
   have first:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.1
   have final:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.2.2
   simpa only [Q6FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
     And.intro first (And.intro old.2.1 final)

theorem kernel_free7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∉wires OwnOneFlagExitQ7.kernelS := by
 by_cases last : i=1542
 · subst i
   simpa only [OwnOneFlagExitQ7.kernelS] using
    Q7FusionPhase.relocated_1542_free _ OneFlagExitSupport.hostS1542_free
 · have prior : i∈[2312,766,765,767,1026,1541] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto
   have old:=q7part31_kernel_free i prior
   change base i∉wires (Q6FusionPhase.relocated OneFlagExitRaw.hostMulS) at old
   rw [←Q7FusionPhase.old_shape] at old
   simp only [Q7FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q7IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq;exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior;omega
   change base i∉wires (Q7FusionPhase.relocated OneFlagExitRaw.hostMulS)
   simp only [Q7FusionPhase.relocated,wires_append,Finset.mem_union,not_or]
   exact ⟨OwnPlusHost.rename_avoid _ _ _ fix old.1,old.2.1,OwnPlusHost.rename_avoid _ _ _ fix old.2.2⟩
private theorem q7part31_logical7 (i : Nat) (hi : i∈[2312,766,765,767,1026,1541,1542]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
 theorem exit_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
 L.core.poolWire k∉wires (OwnOneFlagExitQ7.arithExit L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 2312 1800
     (q7part31_logical7 2312 (by simp)) (by rfl) (kernel_free7 2312 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 766 766
     (q7part31_logical7 766 (by simp)) (by rfl) (kernel_free7 766 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 765 765
     (q7part31_logical7 765 (by simp)) (by rfl) (kernel_free7 765 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 767 767
     (q7part31_logical7 767 (by simp)) (by rfl) (kernel_free7 767 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 1026 770
     (q7part31_logical7 1026 (by simp)) (by rfl) (kernel_free7 1026 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 1541 1285
     (q7part31_logical7 1541 (by simp)) (by rfl) (kernel_free7 1541 (by simp))
 · exact q7part31_placed L hw hn OwnOneFlagExitQ7.kernelS OwnOneFlagExitQ7.kernelS_support 1542 1286
     (q7part31_logical7 1542 (by simp)) (by rfl) (kernel_free7 1542 (by simp))
end ECDSAAdd.Entrant.OneFlagExitOmissions


-- ONEFLAG COMPONENT InventoryNine.lean
open ECDSAAdd ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant.Q7Inventory
attribute [local irreducible] wires
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
open FiniteHostStack FiniteHostFusion

/-- A proof-only witness charges the eighth retired wire, then removes its one unit.
The witness is never part of the emitted circuit. -/
theorem qubits_nine (P : Program)
    (sub : ioWires ∪ wires P ⊆ (WrapperOB5.sites layout).toFinset)
    (free : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285] : List Nat),
      layout.core.poolWire k ∉ wires P)
    (extra : layout.core.poolWire 1286 ∉ wires P) : qubits P ≤ 1592 := by
  let q := layout.core.poolWire 1286
  let witness : Program := [.X q] ++ P
  have qm : q ∈ (WrapperOB5.sites layout).toFinset := by
    apply List.mem_toFinset.mpr
    simp only [q,WrapperOB5.sites,List.mem_append,List.mem_singleton,
      wireBlock,List.mem_map,List.mem_range'_1]
    exact Or.inl (Or.inr ⟨1286,by omega,rfl⟩)
  have ww : wires witness = insert q (wires P) := by
    unfold witness
    rw [wires_append]
    simp only [wires,Instr.wires,Finset.union_empty,Finset.singleton_union]
  have ws : ioWires ∪ wires witness ⊆ (WrapperOB5.sites layout).toFinset := by
    rw [ww]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact sub (Finset.mem_union.mpr (Or.inl hx))
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact qm
      · exact sub (Finset.mem_union.mpr (Or.inr hx))
  have wf : ∀ k ∈ ([1400,1800,766,765,767,1540,770,1285] : List Nat),
      layout.core.poolWire k ∉ wires witness := by
    intro k hk
    rw [ww]
    intro h
    rcases Finset.mem_insert.mp h with he | hp
    · have hkbound : k < 2613 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
      have kne : k ≠ 1286 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
      exact kne (pool_inj layout layout_widths layout_nodup k 1286 hkbound (by omega) he)
    · exact free k hk hp
  have bound := Q6Inventory.qubits_eight witness ws (fun k hk=>wf k (List.mem_append_left [1285] hk)) (wf 1285 (by simp))
  have fresh : q ∉ ioWires ∪ wires P := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact FiniteHostStack.io_avoids_pool 1286 (by omega) h
    · exact extra h
  have sets : ioWires ∪ wires witness = insert q (ioWires ∪ wires P) := by
    rw [ww,Finset.union_insert]
  change (ioWires ∪ wires witness).card ≤ 1593 at bound
  rw [sets,Finset.card_insert_of_notMem fresh] at bound
  change (ioWires ∪ wires P).card ≤ 1592
  omega
end ECDSAAdd.Entrant.Q7Inventory


-- ONEFLAG COMPONENT GenericGeometry7.lean
open ECDSAAdd ECDSAAdd.Entrant
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.GenericQ7Geometry
attribute [local irreducible] wires run
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
open FiniteHostStack FiniteHostFusion FiniteHostFive GenericQ5Geometry
 theorem edges_wrapG_qubits (G : Program)
    (hG : wires G⊆(OB5Support.sites layout).toFinset)
    (hFree : ∀k∈([1800,766,765,767,770] : List Nat),layout.core.poolWire k∉wires G)
    (extra : layout.core.poolWire 1285∉wires G)
    (extra2 : layout.core.poolWire 1286∉wires G)
    (C : Point) (cy : Fp) : qubits (Edges.wrapper layout C cy (wrapG layout G))≤1592 := by
  have supported := Edges.wrapper_support layout layout_widths layout_nodup C cy _
    (wrapG_sites layout layout_widths layout_nodup G hG)
  have sub := Finset.union_subset FiniteHostStack.io_support_original supported
  have edge (k : Nat) (hk : 515≤k ∧ k<2613)
      (old : layout.core.poolWire k∉wires (WrapperOB5.program layout C cy (wrapG layout G))) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    intro h
    rcases Finset.mem_union.mp (Edges.wrapper_wires layout C cy _ h) with h|h
    · exact old h
    · exact Edges.small_away layout layout_widths layout_nodup k hk (Edges.extra_small layout layout_widths layout_nodup C h)
  have omitted (k : Nat) (hk : k∈([1800,766,765,767,770] : List Nat)) :
      layout.core.poolWire k∉wires (Edges.wrapper layout C cy (wrapG layout G)) := by
    have bounds : 515≤k ∧ k<2613 ∧ k≠684 ∧ k≠717 ∧ k≠1400 ∧ k≠1540 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl <;> omega
    apply edge k ⟨bounds.1,bounds.2.1⟩
    exact finWrapper_avoid layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩
      bounds.2.2.1 bounds.2.2.2.1 bounds.2.2.2.2.2 _
      (wrapG_avoid_of_generic layout layout_widths layout_nodup k ⟨bounds.1,bounds.2.1⟩ bounds.2.2.2.2.1 G (hFree k hk)) C cy
  apply Q7Inventory.qubits_nine _ sub
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · apply edge 1400 (by omega)
      exact finWrapper_avoid layout layout_widths layout_nodup 1400 (by omega) (by omega) (by omega) (by omega) (wrapG layout G)
        (spare_not_wrapG layout layout_widths layout_nodup G hG) C cy
    · exact omitted 1800 (by simp)
    · exact omitted 766 (by simp)
    · exact omitted 765 (by simp)
    · exact omitted 767 (by simp)
    · apply edge 1540 (by omega)
      exact finWrapper_avoid1540 layout layout_widths layout_nodup _ (wrapG_noDouble G hG) C cy
    · exact omitted 770 (by simp)
    · apply edge 1285 (by omega)
      exact finWrapper_avoid layout layout_widths layout_nodup 1285 (by omega)
        (by omega) (by omega) (by omega) (wrapG layout G)
        (wrapG_avoid_of_generic layout layout_widths layout_nodup 1285 (by omega)
        (by omega) G extra) C cy
  · apply edge 1286 (by omega)
    exact finWrapper_avoid layout layout_widths layout_nodup 1286 (by omega)
      (by omega) (by omega) (by omega) (wrapG layout G)
      (wrapG_avoid_of_generic layout layout_widths layout_nodup 1286 (by omega)
        (by omega) G extra2) C cy
end ECDSAAdd.Entrant.GenericQ7Geometry


-- ONEFLAG COMPONENT SquareQ7.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OwnDiagAll12PlacedQ7
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires
private theorem q7part34_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1538∉wires (OwnDiagAll12Placed.initial L) := by
  rw [OwnDiagAll12Placed.initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=q7part34_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · have away:=q7part34_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · have away:=q7part34_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1538 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1538 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem q7part34_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)

theorem spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1538∉wires (OwnDiagAll12PlacedQ6.program L) := by
  have p0:=initial_spare_free L hw hn
  have p1 : L.core.poolWire 1538∉wires (OwnDiagAll12Placed.plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 766 1530 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1538∉wires (OwnDiagAll12Placed.guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 765 1531 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1538∉wires (OwnDiagAll12Placed.minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 767 1532 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1538∉wires (OwnDiagAll12Placed.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 770 1536 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  have p5 : L.core.poolWire 1538∉wires (OwnDiagAll12PlacedQ6.program L) :=
    OwnPlusHost.rename_avoid _ _ _ (q7part34_fix L hw hn 1285 1537 1538 (by omega) (by omega) (by omega) (by omega) (by omega)) p4
  exact p5
def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1286) (L.core.poolWire 1538)
def program (L : ControlledPointLayout) : Program := renameProgram (swap L) (OwnDiagAll12PlacedQ6.program L)
attribute [local irreducible] program

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1286
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1538 (by omega)
  · by_cases b:q=L.core.poolWire 1538
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1286 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1286:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1286 (by omega))
  have b:q≠L.core.poolWire 1538:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1538 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b

theorem run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (hin : ∀q∈L.dialogPool,s.basis q=false)
    (hout : ∀q∈L.dialogPool,(run P m s).basis q=false) :
    run (renameProgram (swap L) P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L (swap L) (pool L hw) (outside L hw) P s m ((regValue_zero _ _).mpr hin) ((regValue_zero _ _).mpr hout)

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) := by
  unfold program
  exact OwnDiagAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnDiagAll12PlacedQ6.correct L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=toffoliCount (OwnDiagAll12PlacedQ6.program L) ∧
    measurementCount (program L)=measurementCount (OwnDiagAll12PlacedQ6.program L) := by
  unfold program
  exact renameProgram_counts (swap L) _

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  unfold program
  exact gatePhysical_rename (swap L) (swap L).injective _ (OwnDiagAll12PlacedQ6.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 := by
  unfold program
  exact (Baselines.rename_gateSlots _ _).le.trans (OwnDiagAll12PlacedQ6.slots L hw)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1286∉wires (program L) := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_target_free _ _ _ (spare_free L hw hn)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset := by
  unfold program swap
  exact OwnDiagAll12Placed.swap_support _ _ _ _ (OwnDiagAll12PlacedQ6.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1286
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1538
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286]) :
    L.core.poolWire k∉wires (program L) := by
  by_cases h:k=1286
  · subst k; exact retired_free L hw hn
  have hkold : k∈[1800,766,765,767,770,1285] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    omega
  have f : swap L (L.core.poolWire k)=L.core.poolWire k :=
    q7part34_fix L hw hn 1286 1538 k (by omega) (by omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega) h
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hkold;omega)
  unfold program
  exact OwnPlusHost.rename_avoid _ _ _ f (OwnDiagAll12PlacedQ6.square_free L hw hn k hkold)
end ECDSAAdd.Entrant.OwnDiagAll12PlacedQ7


-- ONEFLAG COMPONENT ProducerOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OneFlagProducer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount fastConstAdd fastConstNeg
 def generic (L : ControlledPointLayout) (P : Program) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnOneFlagEntryQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L) P cx cy
 def gen (L : ControlledPointLayout) (P : Program) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnOneFlagEntryQ7.fusedDivisionF L) (OwnDiagAll12PlacedQ7.program L) P cx cy
 private theorem q7part35_metric_generic (metric : Program→Nat)
   (app : ∀a b,metric (a++b)=metric a+metric b)
   (L : ControlledPointLayout) (D Dold : Fp→Program) (S Sold P Pold : Program)
   (d : ∀k,metric (D k)=metric (Dold k)) (sq : metric S=metric Sold) (p : metric P=metric Pold)
   (cx cy : Fp) : metric (All12Generic.generic L D S P cx cy)=metric (All12Generic.generic L Dold Sold Pold cx cy) := by
  simp only [All12Generic.generic,app]
  rw [d (-cy),sq,p]
 theorem generic_counts_eq (L : ControlledPointLayout) (hw:L.Widths) (P : Program)
   (pc : toffoliCount P=toffoliCount (OwnExitFuseQ6.arithExit L) ∧
         measurementCount P=measurementCount (OwnExitFuseQ6.arithExit L)) (cx cy : Fp) :
   toffoliCount (generic L P cx cy)=toffoliCount (OwnDiagEndpointActual.genericE L cx cy) ∧
   measurementCount (generic L P cx cy)=measurementCount (OwnDiagEndpointActual.genericE L cx cy) := by
  have d (k : Fp) := OwnOneFlagEntryQ7.fusedDivisionF_counts L hw k
  have old (k : Fp) := OwnEndpointEntryQ6.fusedDivisionF_counts L hw k
  have sq := OwnDiagAll12PlacedQ7.counts L hw
  constructor
  · exact q7part35_metric_generic toffoliCount toffoliCount_append L _ _ _ _ _ _
      (fun k=>(d k).1.trans (old k).1.symm) sq.1 pc.1 cx cy
  · exact q7part35_metric_generic measurementCount measurementCount_append L _ _ _ _ _ _
      (fun k=>(d k).2.trans (old k).2.symm) sq.2 pc.2 cx cy
 theorem gen_counts_eq (L : ControlledPointLayout) (hw:L.Widths) (P : Program)
   (pc : toffoliCount P=toffoliCount (OwnExitFuseQ6.arithExit L) ∧
         measurementCount P=measurementCount (OwnExitFuseQ6.arithExit L)) (cx cy : Fp) :
   toffoliCount (gen L P cx cy)=toffoliCount (OwnDiagEndpointActual.genE L cx cy) ∧
   measurementCount (gen L P cx cy)=measurementCount (OwnDiagEndpointActual.genE L cx cy) := by
  have h:=generic_counts_eq L hw P pc cx cy
  simp only [generic,OwnDiagEndpointActual.genericE] at h
  simp only [gen,OwnDiagEndpointActual.genE,All12Generic.gen,All12Generic.mid,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  constructor <;> omega
 theorem square_step (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
   (X Y : Fp) (G : Bool) (origin : BasisState) :
   Triple (PointDialogValues L X Y G origin) (OwnDiagAll12PlacedQ7.program L)
    (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1:Nat) else 0)) Y G origin) := by
  have h:=OwnDiagAll12PlacedQ7.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnDiagAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h
end ECDSAAdd.Entrant.OneFlagProducer


-- ONEFLAG COMPONENT ProducerPropertiesOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OneFlagProducer
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg
 theorem generic_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (ps : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
  wires (generic L P cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (OneFlagEntryProperties.division_support L hw)
   (OwnDiagAll12PlacedQ7.support L hw hn) ps cx cy
 theorem gen_sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (ps : wires P⊆(OB5Support.sites L).toFinset) (cx cy : Fp) :
  wires (gen L P cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen,All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn P ps cx cy)
 theorem gen_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (pp : GatePhysical P) (cx cy : Fp) : GatePhysical (gen L P cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (OneFlagEntryProperties.division_physical L hw hn)
   (OwnDiagAll12PlacedQ7.physical L hw hn) pp cx cy
 theorem gen_slots (L : ControlledPointLayout) (hw:L.Widths) (P : Program)
  (pp : gateSlots P≤20500006) (cx cy : Fp) : gateSlots (gen L P cx cy)≤49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ (OneFlagEntryProperties.division_slots L hw)
   (OwnDiagAll12PlacedQ7.slots L hw) pp cx cy
 theorem generic_free (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (pf : ∀k∈[1800,766,765,767,770,1285,1286],L.core.poolWire k∉wires P)
  (k : Nat) (hk:k∈[1800,766,765,767,770,1285,1286]) (cx cy : Fp) :
  L.core.poolWire k∉wires (generic L P cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
   rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
   (OneFlagEntryProperties.division_free L hw hn k hk)
   (OwnDiagAll12PlacedQ7.square_free L hw hn k hk) (pf k hk) cx cy
 theorem gen_ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (P : Program)
  (halfCorrect : ExitFusionResearch.HalfMultiplyCorrect L P)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
  {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L P cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _ halfCorrect
   (OwnOneFlagEntryQ7.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
   (square_step L hw hn) hc
 theorem gen_qubits (P : Program)
  (ps : wires P⊆(OB5Support.sites layout).toFinset)
  (pf : ∀k∈[1800,766,765,767,770,1285,1286],layout.core.poolWire k∉wires P)
  (C : Point) (cx cy : Fp) : qubits (Edges.wrapper layout C cy (gen layout P cx cy))≤1592 := by
  rw [gen,All12Generic.gen_shape]
  apply GenericQ7Geometry.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup P ps cx cy)
  · intro k hk
    exact generic_free layout layout_widths layout_nodup P pf k (List.mem_append_left [1285,1286] hk) cx cy
  · exact generic_free layout layout_widths layout_nodup P pf 1285 (by simp) cx cy
  · exact generic_free layout layout_widths layout_nodup P pf 1286 (by simp) cx cy
end ECDSAAdd.Entrant.OneFlagProducer


-- ONEFLAG COMPONENT ActualOneFlag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OwnOneFlagActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount
 def generic (L : ControlledPointLayout) (cx cy : Fp) : Program:=
  OneFlagProducer.generic L (OwnOneFlagExitQ7.arithExit L) cx cy
 def gen (L : ControlledPointLayout) (cx cy : Fp) : Program:=
  OneFlagProducer.gen L (OwnOneFlagExitQ7.arithExit L) cx cy
 theorem exit_support (L : ControlledPointLayout) (hw:L.Widths) :
  wires (OwnOneFlagExitQ7.arithExit L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ OwnOneFlagExitQ7.kernelS_support
 theorem exit_counts_eq (L : ControlledPointLayout) :
  toffoliCount (OwnOneFlagExitQ7.arithExit L)=toffoliCount (OwnExitFuseQ6.arithExit L) ∧
  measurementCount (OwnOneFlagExitQ7.arithExit L)=measurementCount (OwnExitFuseQ6.arithExit L) := by
  have a:=OwnOneFlagExitQ7.arithExit_counts L
  have b:=OwnExitFuseQ5.arithExit_counts L
  have c:=Q6ResourceAdapters.exit_counts_eq L
  constructor <;> omega
 theorem counts_eq (L : ControlledPointLayout) (hw:L.Widths) (cx cy : Fp) :
  toffoliCount (gen L cx cy)=toffoliCount (OwnDiagEndpointActual.genE L cx cy) ∧
  measurementCount (gen L cx cy)=measurementCount (OwnDiagEndpointActual.genE L cx cy) :=
  OneFlagProducer.gen_counts_eq L hw _ (exit_counts_eq L) cx cy
 theorem sites (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy : Fp) :
  wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  OneFlagProducer.gen_sites L hw hn _ (exit_support L hw) cx cy
 theorem physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (cx cy : Fp) :
  GatePhysical (gen L cx cy) :=
  OneFlagProducer.gen_physical L hw hn _ (OwnOneFlagExitQ7.arithExit_physical L hw hn) cx cy
 theorem slots (L : ControlledPointLayout) (hw:L.Widths) (cx cy : Fp) :
  gateSlots (gen L cx cy)≤49200000 :=
  OneFlagProducer.gen_slots L hw _ (OwnOneFlagExitQ7.arithExit_slots_le L) cx cy
 theorem ok (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
  (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
  (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
  (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
  {cx cy : Fp} (hc:curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
  OneFlagProducer.gen_ok L hw hn _ (OwnOneFlagExitQ7.arithExit_correct L hw hn)
   logicalND hlo logicalAway logicalReplay hc
 theorem qubits (C : Point) (cx cy : Fp) : qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1592 :=
  OneFlagProducer.gen_qubits _ (exit_support layout layout_widths)
   (OneFlagExitOmissions.exit_avoids layout layout_widths layout_nodup) C cx cy
end ECDSAAdd.Entrant.OwnOneFlagActual


section
-- Verified component DHDefinitions
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnSharedDH

def flipIf (v : Bool) (w : Wire) : Program := if v then [.X w] else []

/-- `d ^= enD ∧ c ∧ f ∧ ¬g ∧ [xk = cx] ∧ [y0 = cy]` and `h ^= enH ∧ c ∧ f ∧ ¬g ∧ [xk ≠ cx]`,
with clean ancillas `a1 a2 a3` (restored). Self-inverse, measurement-free. -/
def gadget (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) : Program :=
  [.CCX c f a1, .X g, .CCX a1 g a2, .X g] ++
  ((if enD then
     flipIf (!cx) xk ++ [.CCX a2 xk a3] ++ flipIf (!cx) xk ++
     flipIf (!cy) y0 ++ [.CCX a3 y0 d] ++ flipIf (!cy) y0 ++
     (if enH then [.CX a2 h, .CX a3 h] else []) ++
     flipIf (!cx) xk ++ [.measureX a3 [] [.CZ a2 xk]] ++ flipIf (!cx) xk
   else []) ++
  ((if enH && !enD then flipIf cx xk ++ [.CCX a2 xk h] ++ flipIf cx xk else []) ++
  [.X g, .measureX a2 [] [.CZ a1 g], .X g, .measureX a1 [] [.CZ c f]]))

end OwnSharedDH
end ECDSAAdd.Entrant

end

section
-- Verified component AndPrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 theorem erase (t a b : Wire) (x : Bool) (s : State) (ha:a≠t) (hb:b≠t)
  (h:s.basis t=(s.basis a && s.basis b)) :
  measureAndCorrect t [] [.CZ a b] x s=⟨s.phase,writeBit s.basis t false⟩ := by
  obtain ⟨ph,bs⟩:=s
  simp only at h
  cases x <;> simp [measureAndCorrect,correct,writeBit,Function.update_apply,ha,hb,h]
 def clearMatch (a x t : Wire) (cx : Bool) : Program :=
  flipIf (!cx) x ++ [.measureX t [] [.CZ a x]] ++ flipIf (!cx) x
 def computeMatch (a x t : Wire) (cx : Bool) : Program :=
  flipIf (!cx) x ++ [.CCX a x t] ++ flipIf (!cx) x
 theorem compute_match (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (zero:s.basis t=false) :
  run (computeMatch a x t cx) m s=
    ⟨s.phase,writeBit s.basis t (s.basis a && (s.basis x==cx))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      by_cases qt:q=t
      · subst q
        simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
      · by_cases qx:q=x
        · subst q
          simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
        · simp [computeMatch,flipIf,run,writeBit,Function.update_apply,qt,qx,ax,ant,xt,Ne.symm ant,Ne.symm xt,zero]
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      simp [computeMatch,flipIf,run,writeBit,zero]
 theorem compute_toggle (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) :
  run (computeMatch a x t cx) m s=
    ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && (s.basis x==cx)))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      by_cases qt:q=t
      · subst q
        simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt]
      · by_cases qx:q=x
        · subst q
          simp [computeMatch,flipIf,run,writeBit,Function.update_apply,ax,ant,xt,Ne.symm ant,Ne.symm xt]
        · simp [computeMatch,flipIf,run,writeBit,Function.update_apply,qt,qx,ax,ant,xt,Ne.symm ant,Ne.symm xt]
  · apply State.extensionality
    · simp [computeMatch,flipIf,run]
    · funext q
      simp [computeMatch,flipIf,run,writeBit]
 theorem clear_match (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (clearMatch a x t cx) m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant⟩,xt,_⟩:=hn
  cases cx
  · let v : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
    have vt : v.basis t=(v.basis a && v.basis x) := by
     simp [v,writeBit,Function.update_apply,ant,xt,ax,Ne.symm xt] at value ⊢
     exact value
    have e:=erase t a x (m.headD false) v ant xt vt
    simp only [clearMatch,flipIf,Bool.not_false,if_true,List.cons_append,List.nil_append,run]
    rw [show {phase:=s.phase,basis:=writeBit s.basis x (!s.basis x)}=v by rfl,e]
    apply State.extensionality
    · rfl
    · funext q
      by_cases qt:q=t
      · subst q;simp [v,writeBit,Function.update_apply,Ne.symm xt]
      · by_cases qx:q=x
        · subst q;simp [v,writeBit,Function.update_apply,xt]
        · simp [v,writeBit,Function.update_apply,qt,qx]
  · have e:=erase t a x (m.headD false) s ant xt (by simpa using value)
    simpa [clearMatch,flipIf,run] using e
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component SharedWindow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def hShared (a t h : Wire) : Program := [.CX a h,.CX t h]
 def hOld (a x h : Wire) (cx : Bool) : Program := flipIf cx x ++ [.CCX a x h] ++ flipIf cx x
 theorem h_eq (a x t h : Wire) (cx : Bool) (hn:[a,x,t,h].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (hShared a t h) m s=run (hOld a x h cx) m s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨ax,ant,ah⟩,⟨xt,xh⟩,th,_⟩:=hn
  cases cx <;> apply State.extensionality
  all_goals try simp [hShared,hOld,flipIf,run]
  all_goals
   funext q
   by_cases qh:q=h
   · subst q
     simp only [hShared,hOld,flipIf,Bool.false_eq_true,if_false,if_true,List.nil_append,List.append_nil,
       List.cons_append,run,writeBit,Function.update_self,Function.update_of_ne (Ne.symm th),Function.update_of_ne (Ne.symm ah)]
     simp [writeBit,Function.update_apply,ax,ant,ah,xt,xh,th,Ne.symm xh,Ne.symm ax,value]
     all_goals cases s.basis a <;> cases s.basis x <;> rfl
   · by_cases qx:q=x
     · subst q
       simp [hShared,hOld,flipIf,run,writeBit,Function.update_apply,qh,xh,Ne.symm xh,ax,Ne.symm ax]
     · simp [hShared,hOld,flipIf,run,writeBit,Function.update_apply,qh,qx,xh,Ne.symm xh,ax,Ne.symm ax]
 theorem run_write_outside (p : Program) (port : Wire) (hp:port∉wires p)
  (s : State) (m : List Bool) (value : Bool) :
  run p m ⟨s.phase,writeBit s.basis port value⟩=
   ⟨(run p m s).phase,writeBit (run p m s).basis port value⟩ := by
  have h:=pool_run_agrees p (wires p) (Finset.Subset.refl _) m
    ⟨s.phase,writeBit s.basis port value⟩ s rfl (by
     intro q hq
     exact Function.update_of_ne (show q≠port from fun he=>hp (he ▸ hq)) _ _)
  apply State.extensionality
  · exact h.1
  funext q
  by_cases used:q∈wires p
  · change _=writeBit (run p m s).basis port value q
    rw [show writeBit (run p m s).basis port value q=(run p m s).basis q from
      Function.update_of_ne (show q≠port from fun he=>hp (he ▸ used)) _ _]
    exact h.2 q used
  · rw [run_preserves_outside p m _ q used]
    change writeBit s.basis port value q=writeBit (run p m s).basis port value q
    by_cases eq:q=port
    · subst q;simp [writeBit]
    · simp only [writeBit,Function.update_of_ne eq,run_preserves_outside p m s q used]
 theorem zero_records (P : Program) (h:measurementCount P=0) (s : State) (m n : List Bool) :
  run P m s=run P n s := by
  rw [←run_take P m s,←run_take P n s,h]
  rfl
 theorem window_eq (a x t h : Wire) (cx : Bool) (hn:[a,x,t,h].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(s.basis a && (s.basis x==cx))) :
  run (hShared a t h++clearMatch a x t cx) m s=
   run (clearMatch a x t cx++hOld a x h cx) m s := by
  have nd3 : [a,x,t].Nodup := List.Nodup.of_append_left (show ([a,x,t]++[h]).Nodup from hn)
  have facts:=hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
  obtain ⟨⟨ax,ant,ah⟩,⟨xt,xh⟩,th,_⟩:=facts
  have keep (q : Wire) (qh:q=a∨q=x∨q=t) :
    (run (hShared a t h) m s).basis q=s.basis q := by
    simp only [hShared,run]
    rcases qh with rfl|rfl|rfl <;> simp [writeBit,Function.update_apply,ah,xh,th]
  have v : (run (hShared a t h) m s).basis t=
      ((run (hShared a t h) m s).basis a && ((run (hShared a t h) m s).basis x==cx)) := by
    rw [keep t (Or.inr (Or.inr rfl)),keep a (Or.inl rfl),keep x (Or.inr (Or.inl rfl))]
    exact value
  have hzero:measurementCount (hShared a t h)=0:=by simp [hShared,measurementCount]
  have oldzero:measurementCount (hOld a x h cx)=0:=by cases cx <;> simp [hOld,flipIf,measurementCount]
  have oldaway:t∉wires (hOld a x h cx) := by
    cases cx <;> simp [hOld,flipIf,wires,Instr.wires,Ne.symm ant,Ne.symm xt,th]
  rw [run_append,run_append,run_take (hShared a t h) m s,run_take (clearMatch a x t cx) m s,
    hzero,List.drop_zero,clear_match a x t cx nd3 _ m v,clear_match a x t cx nd3 s _ value]
  rw [zero_records _ oldzero _ _ m,run_write_outside _ _ oldaway]
  rw [h_eq a x t h cx hn s m value]
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component SharedGadget
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def prepPrefix (c f g a1 a2 : Wire) : Program := [.CCX c f a1,.X g,.CCX a1 g a2,.X g]
 def prepare (c f g d x y a1 a2 a3 : Wire) (cx cy : Bool) : Program :=
  prepPrefix c f g a1 a2 ++ (computeMatch a2 x a3 cx ++ computeMatch a3 y d cy)
 def tail (c f g a1 a2 : Wire) : Program := [.X g,.measureX a2 [] [.CZ a1 g],.X g,.measureX a1 [] [.CZ c f]]
 theorem new_shape (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool) :
  gadget c f g d h x y a1 a2 a3 true true cx cy=
   prepare c f g d x y a1 a2 a3 cx cy ++
    ((hShared a2 a3 h++clearMatch a2 x a3 cx)++tail c f g a1 a2) := by
  simp only [gadget,prepare,prepPrefix,tail,hShared,clearMatch,computeMatch,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,if_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
 theorem old_shape (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool) :
  DHGadget.gadget c f g d h x y a1 a2 a3 true true cx cy=
   prepare c f g d x y a1 a2 a3 cx cy ++
    ((clearMatch a2 x a3 cx++hOld a2 x h cx)++tail c f g a1 a2) := by
  simp only [DHGadget.gadget,prepare,prepPrefix,tail,hOld,clearMatch,computeMatch,flipIf,DHGadget.flipIf,
    if_true,List.append_assoc]
 theorem ready (c f g d h x y a1 a2 a3 : Wire) (cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool) (z:s.basis a3=false) :
  (run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis a3=
   ((run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis a2 &&
    ((run (prepare c f g d x y a1 a2 a3 cx cy) m s).basis x==cx)) := by
  have first:a3∉wires (prepPrefix c f g a1 a2) := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
   simp [prepPrefix,wires,Instr.wires]
   tauto
  have nd:[a2,x,a3].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndD:[a3,y,d].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ad:a3≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have a2d:a2≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have xd:x≠d:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have a2a3:a2≠a3:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have xa3:x≠a3:=by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn;tauto
  have pm:measurementCount (prepPrefix c f g a1 a2)=0:=by simp [prepPrefix,measurementCount]
  have cm:measurementCount (computeMatch a2 x a3 cx)=0:=by cases cx <;> simp [computeMatch,flipIf,measurementCount]
  let v:=run (prepPrefix c f g a1 a2) m s
  have zero:v.basis a3=false:=(run_preserves_outside _ _ _ _ first).trans z
  have cEq:=compute_match a2 x a3 cx nd v m zero
  let w:=run (computeMatch a2 x a3 cx) m v
  have dEq:=compute_toggle a3 y d cy ndD w m
  simp only [prepare,run_append,run_take,pm,cm,List.drop_zero]
  simp only [List.take_zero,zero_records _ pm s [] m,zero_records _ cm _ [] m]
  change (run (computeMatch a3 y d cy) m w).basis a3=
   ((run (computeMatch a3 y d cy) m w).basis a2 && ((run (computeMatch a3 y d cy) m w).basis x==cx))
  rw [dEq]
  simp only [writeBit,Function.update_of_ne ad,Function.update_of_ne a2d,Function.update_of_ne xd]
  change (run (computeMatch a2 x a3 cx) m v).basis a3=
   ((run (computeMatch a2 x a3 cx) m v).basis a2 && ((run (computeMatch a2 x a3 cx) m v).basis x==cx))
  rw [cEq]
  simp [writeBit,Function.update_apply,a2a3,xa3]
 theorem context_congr (P A B Q : Program) (s : State) (m : List Bool)
  (mc:measurementCount A=measurementCount B)
  (eq:∀n,run A n (run P (m.take (measurementCount P)) s)=run B n (run P (m.take (measurementCount P)) s)) :
  run (P++(A++Q)) m s=run (P++(B++Q)) m s := by
  simp only [run_append]
  rw [mc,eq]
 theorem gadget_eq (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z:s.basis a3=false) :
  run (gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s=
   run (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s := by
  cases enD <;> cases enH
  · rfl
  · rfl
  · simp only [gadget,DHGadget.gadget,flipIf,DHGadget.flipIf,if_true,if_false,Bool.not_false,Bool.false_and,Bool.false_eq_true,List.append_nil]
  · rw [new_shape,old_shape]
    apply context_congr
    · cases cx <;> simp [hShared,hOld,clearMatch,flipIf,measurementCount]
    · intro n
      have nd:[a2,x,a3,h].Nodup := by
       simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
      exact window_eq a2 x a3 h cx nd _ n (ready c f g d h x y a1 a2 a3 cx cy hn s _ z)
 theorem gadget_run_fast (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) (z3:s.basis a3=false) :
  run (gadget c f g d h x y a1 a2 a3 enD enH cx cy) m s=⟨s.phase,fun q=>
   if q=d then s.basis d ^^ (enD && s.basis c && s.basis f && !s.basis g && (s.basis x==cx) && (s.basis y==cy))
   else if q=h then s.basis h ^^ (enH && s.basis c && s.basis f && !s.basis g && (s.basis x != cx))
   else s.basis q⟩ := by
  rw [gadget_eq c f g d h x y a1 a2 a3 enD enH cx cy hn s m z3]
  exact DHGadget.gadget_run c f g d h x y a1 a2 a3 enD enH cx cy hn s m z1 z2 z3
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component MeasuredDefinitions
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnMeasuredDH
open DHGadget
def gadgetM (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) : Program :=
  [.CCX c f a1, .X g, .CCX a1 g a2, .X g] ++
  ((if enD then
     flipIf (!cx) xk ++ [.CCX a2 xk a3] ++ flipIf (!cx) xk ++
     flipIf (!cy) y0 ++ [.measureX d [] [.CZ a3 y0]] ++ flipIf (!cy) y0 ++
     flipIf (!cx) xk ++ [.measureX a3 [] [.CZ a2 xk]] ++ flipIf (!cx) xk
   else []) ++
  ((if enH then flipIf cx xk ++ [.measureX h [] [.CZ a2 xk]] ++ flipIf cx xk else []) ++
  [.X g, .measureX a2 [] [.CZ a1 g], .X g, .measureX a1 [] [.CZ c f]]))


end OwnMeasuredDH
end ECDSAAdd.Entrant

end

section
-- Verified component PrefixState
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 theorem prefix_run (c f g a1 a2 : Wire) (hn:[c,f,g,a1,a2].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) :
  run (prepPrefix c f g a1 a2) m s=⟨s.phase,
   writeBit (writeBit s.basis a1 (s.basis c && s.basis f)) a2 (s.basis c && s.basis f && !s.basis g)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  obtain ⟨⟨cf,cg,ca1,ca2⟩,⟨fg,fa1,fa2⟩,⟨ga1,ga2⟩,a12,_⟩:=hn
  apply State.extensionality
  · simp [prepPrefix,run]
  · funext q
    by_cases qa1:q=a1
    · subst q
      simp [prepPrefix,run,writeBit,Function.update_apply,ca1,ca2,fa1,fa2,ga1,ga2,a12,
       Ne.symm ca1,Ne.symm ca2,Ne.symm fa1,Ne.symm fa2,Ne.symm ga1,Ne.symm ga2,Ne.symm a12,z1,z2]
    · by_cases qa2:q=a2
      · subst q
        simp [prepPrefix,run,writeBit,Function.update_apply,ca1,ca2,fa1,fa2,ga1,ga2,a12,
         Ne.symm ca1,Ne.symm ca2,Ne.symm fa1,Ne.symm fa2,Ne.symm ga1,Ne.symm ga2,Ne.symm a12,z1,z2]
      · by_cases qg:q=g
        · subst q
          simp [prepPrefix,run,writeBit,Function.update_apply,qa1,qa2,ga1,ga2]
        · simp [prepPrefix,run,writeBit,Function.update_apply,qa1,qa2,qg,ga1,ga2,Ne.symm ga2]
 theorem bne_match (x cx : Bool) : (x != cx)=(x==!cx) := by
  cases x <;> cases cx <;> rfl
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component ConditionalStages
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnSharedDH
open Arithmetic
 def clearIf (en : Bool) (a x t : Wire) (cx : Bool) : Program := if en then clearMatch a x t cx else []
 theorem clear_if (en : Bool) (a x t : Wire) (cx : Bool) (hn:[a,x,t].Nodup)
  (s : State) (m : List Bool) (value:s.basis t=(en && s.basis a && (s.basis x==cx))) :
  run (clearIf en a x t cx) m s=⟨s.phase,writeBit s.basis t false⟩ := by
  cases en
  · simp only [Bool.false_and] at value
    apply State.extensionality
    · rfl
    · funext q
      simp only [clearIf,Bool.false_eq_true,if_false,run]
      by_cases qt:q=t
      · subst q;simp [writeBit,value]
      · simp [writeBit,Function.update_apply,qt]
  · exact clear_match a x t cx hn s m (by simpa using value)
 def dStage (en : Bool) (a x y t d : Wire) (cx cy : Bool) : Program :=
  if en then computeMatch a x t cx ++ (clearMatch t y d cy ++ clearMatch a x t cx) else []
 theorem d_stage (en : Bool) (a x y t d : Wire) (cx cy : Bool) (hn:[a,x,y,t,d].Nodup)
  (s : State) (m : List Bool) (zero:s.basis t=false)
  (value:s.basis d=(en && s.basis a && (s.basis x==cx) && (s.basis y==cy))) :
  run (dStage en a x y t d cx cy) m s=⟨s.phase,writeBit s.basis d false⟩ := by
  cases en
  · simp only [Bool.false_and] at value
    apply State.extensionality
    · rfl
    · funext q
      simp only [dStage,Bool.false_eq_true,if_false,run]
      by_cases qd:q=d
      · subst q;simp [writeBit,value]
      · simp [writeBit,Function.update_apply,qd]
  · simp only [Bool.true_and] at value
    have ndC:[a,x,t].Nodup := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
    have ndD:[t,y,d].Nodup := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
    have facts:=hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
    obtain ⟨⟨ax,ay,ant,ad⟩,⟨xy,xt,xd⟩,⟨yt,yd⟩,td,_⟩:=facts
    let w : State:=⟨s.phase,writeBit s.basis t (s.basis a && (s.basis x==cx))⟩
    let u : State:=⟨w.phase,writeBit w.basis d false⟩
    have ce (n : List Bool) : run (computeMatch a x t cx) n s=w := compute_match a x t cx ndC s n zero
    have wd : w.basis d=(w.basis t && (w.basis y==cy)) := by
      simpa only [w,writeBit,Function.update_of_ne (Ne.symm td),Function.update_self,Function.update_of_ne yt] using value
    have de (n : List Bool) : run (clearMatch t y d cy) n w=u := clear_match t y d cy ndD w n wd
    have ut : u.basis t=(u.basis a && (u.basis x==cx)) := by
      simp only [u,w,writeBit,Function.update_of_ne td,Function.update_of_ne ad,
       Function.update_of_ne xd,Function.update_self,Function.update_of_ne ant,Function.update_of_ne xt]
    have ae (n : List Bool) : run (clearMatch a x t cx) n u=⟨u.phase,writeBit u.basis t false⟩ :=
      clear_match a x t cx ndC u n ut
    simp only [dStage,if_true,run_append,ce,de,ae]
    apply State.extensionality
    · rfl
    · funext q
      by_cases qt:q=t
      · subst q;simp [u,w,writeBit,Function.update_apply,td,zero]
      · by_cases qd:q=d
        · subst q;simp [u,w,writeBit,Function.update_apply,qt]
        · simp [u,w,writeBit,Function.update_apply,qt,qd]
end ECDSAAdd.Entrant.OwnSharedDH

end

section
-- Verified component MeasuredGadget
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnMeasuredDH
open Arithmetic OwnSharedDH
 theorem shape (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  gadgetM c f g d h x y a1 a2 a3 enD enH cx cy=
   prepPrefix c f g a1 a2 ++ (dStage enD a2 x y a3 d cx cy ++
    (clearIf enH a2 x h (!cx) ++ (clearMatch a1 g a2 false ++ clearMatch c f a1 true))) := by
  simp only [gadgetM,prepPrefix,dStage,clearIf,computeMatch,clearMatch,flipIf,DHGadget.flipIf,
   Bool.not_not,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
   List.nil_append,List.append_nil,List.append_assoc,List.cons_append]
 theorem gadgetM_run_fast (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool)
  (hn:[f,x,y,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
  (z1:s.basis a1=false) (z2:s.basis a2=false) (z3:s.basis a3=false)
  (hd:s.basis d=(enD && s.basis c && s.basis f && !s.basis g && (s.basis x==cx) && (s.basis y==cy)))
  (hh:s.basis h=(enH && s.basis c && s.basis f && !s.basis g && (s.basis x != cx))) :
  run (gadgetM c f g d h x y a1 a2 a3 enD enH cx cy) m s=⟨s.phase,fun q=>
   if q=d then false else if q=h then false else s.basis q⟩ := by
  have ndP:[c,f,g,a1,a2].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndD:[a2,x,y,a3,d].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndH:[a2,x,h].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndA2:[a1,g,a2].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have ndA1:[c,f,a1].Nodup := by
   simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn ⊢;tauto
  have facts:=hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at facts
  obtain ⟨⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩,⟨m1,m2,m3,m4,m5,m6,m7,m8⟩,⟨k1,k2,k3,k4,k5,k6,k7⟩,
    ⟨l1,l2,l3,l4,l5,l6⟩,⟨p1,p2,p3,p4,p5⟩,⟨q1,q2,q3,q4⟩,⟨r1,r2,r3⟩,⟨t1,t2⟩,t3,_⟩:=facts
  let v : State:=⟨s.phase,writeBit (writeBit s.basis a1 (s.basis c && s.basis f)) a2
    (s.basis c && s.basis f && !s.basis g)⟩
  let u : State:=⟨v.phase,writeBit v.basis d false⟩
  let k : State:=⟨u.phase,writeBit u.basis h false⟩
  let l : State:=⟨k.phase,writeBit k.basis a2 false⟩
  have pe (n : List Bool) : run (prepPrefix c f g a1 a2) n s=v := prefix_run c f g a1 a2 ndP s n z1 z2
  have vz : v.basis a3=false := by
   simp [v,writeBit,Function.update_apply,Ne.symm t2,Ne.symm t3,z3]
  have vd : v.basis d=(enD && v.basis a2 && (v.basis x==cx) && (v.basis y==cy)) := by
   simpa [v,writeBit,Function.update_apply,p3,p4,m6,m7,k5,k6,Bool.and_assoc] using hd
  have de (n : List Bool) : run (dStage enD a2 x y a3 d cx cy) n v=u :=
   d_stage enD a2 x y a3 d cx cy ndD v n vz vd
  have uh : u.basis h=(enH && u.basis a2 && (u.basis x==!cx)) := by
   simpa [u,v,writeBit,Function.update_apply,r2,r1,m3,m4,m6,m7,Ne.symm p4,Ne.symm p2,k5,k6,r2,
    Bool.and_assoc,bne_match] using hh
  have he (n : List Bool) : run (clearIf enH a2 x h (!cx)) n u=k := clear_if enH a2 x h (!cx) ndH u n uh
  have ka2 : k.basis a2=(k.basis a1 && (k.basis g==false)) := by
   simp [k,u,v,writeBit,Function.update_apply,Ne.symm r2,Ne.symm p4,Ne.symm p3,Ne.symm r1,
    Ne.symm q2,Ne.symm q3,t1,q1,Ne.symm p1,q2,q3,Bool.and_assoc]
  have a2e (n : List Bool) : run (clearMatch a1 g a2 false) n k=l := clear_match a1 g a2 false ndA2 k n ka2
  have la1 : l.basis a1=(l.basis c && (l.basis f==true)) := by
   simp [l,k,u,v,writeBit,Function.update_apply,t1,Ne.symm r1,Ne.symm p3,l4,l5,n7,n8,n4,n6,
    Ne.symm t1,l3,l1,Bool.and_assoc]
  have a1e (n : List Bool) : run (clearMatch c f a1 true) n l=⟨l.phase,writeBit l.basis a1 false⟩ :=
   clear_match c f a1 true ndA1 l n la1
  simp only [shape,run_append,pe,de,he,a2e,a1e]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qd:q=d
    · subst q;simp [l,k,u,v,writeBit,Function.update_apply,p3,p4,p2]
    · by_cases qh:q=h
      · subst q;simp [l,k,u,v,writeBit,Function.update_apply,r1,r2]
      · by_cases qa1:q=a1
        · subst q;simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,z1]
        · by_cases qa2:q=a2
          · subst q;simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,qa1,z2]
          · simp [l,k,u,v,writeBit,Function.update_apply,qd,qh,qa1,qa2]
end ECDSAAdd.Entrant.OwnMeasuredDH

end

section
-- Verified component CompleteProperties
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic
namespace OwnSharedDH
set_option maxHeartbeats 4000000 in
theorem gadget_wires (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) (q : Wire)
    (hq : q ∈ wires (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy)) :
    q = c ∨ q = f ∨ q = g ∨ q = d ∨ q = h ∨ q = xk ∨ q = y0 ∨ q = a1 ∨ q = a2 ∨ q = a3 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, wires, Instr.wires, correctionWires] at hq <;> tauto

theorem gadget_counts (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 4 ∧
    measurementCount (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 3 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, toffoliCount, measurementCount]

theorem gadget_gateSlots (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    Challenge.gateSlots (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 33 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf, Challenge.gateSlots, Challenge.instructionSlots]

theorem gadget_physical (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) :
    GatePhysical (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  intro i hi
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadget, flipIf] at hi <;> rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [RecordedQuantum.PhysicalInstr, ProperGate, eq_comm]


end OwnSharedDH
namespace OwnMeasuredDH
open DHGadget
/-- When the gadget only clears `d` and `h`, the measured variant has the same run. -/
theorem gadgetM_eq (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
    (z1 : s.basis a1 = false) (z2 : s.basis a2 = false) (z3 : s.basis a3 = false)
    (hd : (s.basis d ^^ (enD && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk == cx) && (s.basis y0 == cy))) = false)
    (hh : (s.basis h ^^ (enH && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk != cx))) = false) :
    run (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s =
      run (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s := by
  have hd' : s.basis d = (enD && s.basis c && s.basis f && !s.basis g &&
      (s.basis xk == cx) && (s.basis y0 == cy)) := by
    revert hd; cases s.basis d <;> simp
  have hh' : s.basis h = (enH && s.basis c && s.basis f && !s.basis g && (s.basis xk != cx)) := by
    revert hh; cases s.basis h <;> simp
  rw [gadgetM_run_fast c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3 hd' hh',
    gadget_run c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3]
  congr 1
  funext q
  split_ifs
  · exact hd.symm
  · exact hh.symm
  · rfl

theorem gadgetM_wires (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) (q : Wire)
    (hq : q ∈ wires (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy)) :
    q ∈ wires (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, gadget, flipIf, wires, Instr.wires, correctionWires] at hq ⊢ <;> tauto

theorem gadgetM_counts (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 3 ∧
    measurementCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 5 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf, toffoliCount, measurementCount]

theorem gadgetM_gateSlots (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    Challenge.gateSlots (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 35 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf, Challenge.gateSlots, Challenge.instructionSlots]

theorem gadgetM_physical (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) :
    GatePhysical (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  intro i hi
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf] at hi <;> rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [RecordedQuantum.PhysicalInstr, ProperGate, eq_comm]


end OwnMeasuredDH
namespace OwnDHComposition
 theorem combined_budget (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (OwnMeasuredDH.gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) +
    toffoliCount (OwnSharedDH.gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 7 :=
  Nat.add_le_add (OwnMeasuredDH.gadgetM_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
    (OwnSharedDH.gadget_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
 theorem exact_active_costs (c f g d h xk y0 a1 a2 a3 : Wire) (cx cy : Bool) :
    toffoliCount (OwnMeasuredDH.gadgetM c f g d h xk y0 a1 a2 a3 true true cx cy)=3 ∧
    toffoliCount (OwnSharedDH.gadget c f g d h xk y0 a1 a2 a3 true true cx cy)=4 := by
  cases cx <;> cases cy <;> simp [OwnMeasuredDH.gadgetM, DHGadget.flipIf,
    OwnSharedDH.gadget,OwnSharedDH.flipIf,toffoliCount]
end OwnDHComposition
end ECDSAAdd.Entrant

end

section
-- Verified component Callers
open ECDSAAdd ECDSAAdd.Entrant
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
attribute [local irreducible] run wires
 def clrClear (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  OwnMeasuredDH.gadgetM L.control L.point.finite L.genericSelect L.doubleSelect L.core.equalNegY
    (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1) (L.core.poolWire 2)
    (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C)
 def clrRestore (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  OwnSharedDH.gadget L.control L.point.finite L.genericSelect L.doubleSelect L.core.equalNegY
    (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1) (L.core.poolWire 2)
    (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C)
section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem clrClear_flag (C : Point) (cy : Fp) (R : Point) (b D G H : Bool)
    (hD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))))
    (hH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C)))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrClear L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false false G false false false false)) := by
  intro s m v
  have post := clrDH_flag L hw hn C cy R b D G H false false hD hH s m v
  have nd := dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C)
  have pool3 : ∀ i, i < 3 → s.basis (L.core.poolWire i) = false := by
    intro i hi
    apply (regValue_zero _ _).mp v.clean
    have mem : L.core.poolWire i ∈ L.dialogPool.take 3 := by
      rw [pool_block L hw 3 (by omega)]
      exact List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩
    exact List.mem_of_mem_take mem
  have hrun := DHGadget.gadget_run L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega))
  have hr' := dialogFlagState_read L hn false false G false false false false
  have outD := (post.2.flags L.doubleSelect (by simp [inPlaceFlags])).trans hr'.2.1
  have outH := (post.2.flags L.core.equalNegY (by simp [inPlaceFlags])).trans hr'.2.2.2.2.2.1
  have dg : L.doubleSelect ≠ L.core.equalNegY := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
    exact nd.2.2.2.2.1.2.1
  change (run (DHGadget.gadget _ _ _ _ _ _ _ _ _ _ _ _ _ _) m s).basis _ = _ at outD outH
  rw [hrun] at outD outH
  simp only [if_true, if_neg (Ne.symm dg)] at outD outH
  have heq := OwnMeasuredDH.gadgetM_eq L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega)) outD outH
  unfold clrClear
  rw [heq]
  exact post

theorem clrRestore_flag (C : Point) (cy : Fp) (R : Point) (b D G H D' H' : Bool)
    (hD : D' = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))))
    (hH : H' = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C)))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrRestore L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false D' G false false H' false)) := by
  intro s m v
  have nd:=dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C)
  have zero:s.basis (L.core.poolWire 2)=false := by
   apply (regValue_zero _ _).mp v.clean
   apply List.mem_of_mem_take (i:=3)
   rw [pool_block L hw 3 (by omega)]
   exact List.mem_map.mpr ⟨2,List.mem_range'_1.mpr ⟨by omega,by omega⟩,rfl⟩
  have eq:=OwnSharedDH.gadget_eq L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m zero
  have old:=clrDH_flag L hw hn C cy R b D G H D' H' hD hH s m v
  unfold clrRestore
  rw [eq]
  exact old
end
end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component WholeSemantics
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum Edges
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires
def finiteProgram (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  inputClass L C cy ++
  genFlagN L ++ clrClear L C cy ++
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
  clrRestore L C cy ++ mergeFlagsN L ++
  renameProgram (sigP L) (corners2 L C ++ Edges.shared L C) ++
  chainErase L.control L.point.finite L.genericSelect

private theorem dh3_10_equal_simp [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgram L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,dh3_10_equal_simp,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,dh3_10_equal_simp]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,dh3_10_equal_simp]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,dh3_10_equal_simp]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,dh3_10_equal_simp]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have hI1 : (((G ^^ (b && pointFinite R1)) ^^ D) ^^ H) = I := by
    rw [hR1fin, ← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := inputClass_flag L hw hn R C cy b false false false false false false false
  rw [hD,hI,hH,Bool.false_xor,Bool.false_xor,Bool.false_xor] at h3
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have hHx : H = true → b = true ∧ D = false := by
    intro h
    dsimp only [H, D, dialogException, dialogDouble] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hb, _, hne, _⟩, hR⟩ := h
    refine ⟨hb, ?_⟩
    simp [hR, hne]
  have hDx : D = true → b = true := by
    intro h
    dsimp only [D, dialogDouble] at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have cls := DHClass.classify hc b R
  dsimp only at cls
  have hKC : decide (cy≠-cy) = decide (C≠-C) := by
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact doubling_enabled_iff hc
  have clrD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))) := by
    rw [hKC]; simp only [D, G, C]; rw [← cls.1, Bool.xor_self]
  have clrH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    rw [hE]; simp only [H, G, C]; rw [← cls.2, Bool.xor_self]
  have hf1 := clrClear_flag L hw hn C cy R b D G H clrD clrH
  have read := dialogFlagState_read L hn false false G false false false false
  have h7 := genericD_ok L hw hn hc Gen hGen R b
    (dialogFlagState L false false G false false false false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2) read.2.2.2.2.2.1 read.2.1
  rw [read.2.2.1] at h7
  have resD : D = (false ^^ (decide (cy≠-cy) && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R1 == yBit C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [D, C]; rw [cls.1]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hKC, Bool.false_xor]; simp only [D, G, C]; exact cls.1
  have resH : H = (false ^^ (exceptionBit C && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [H, C]; rw [cls.2]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hE, Bool.false_xor]; simp only [H, G, C]; exact cls.2
  have hu := clrRestore_flag L hw hn C cy R1 b false G false D H resD resH
  have h9 := genFlagN_flag L hn R1 b false D G false false H false
  rw [hI1] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,dh3_10_equal_simp] using hf.2.2.2
  have h10 := Edges.shared_flag L hw hn S C b false D I O false H false
  have hdo : (b && pointEqual S (C+C))=D := by
    have hcy : decide (cy≠-cy)=true := by rw [cy_ne_neg hc]
    have hk : K=b := by simp [K,hcy]
    rw [←hk,hK]
    simpa only [dh3_10_equal_simp] using hf.2.1
  rw [heout,hdo,Bool.xor_self,Bool.xor_self] at h10
  simp only [dh3_10_equal_simp] at h10
  rw [hf.1,Bool.xor_self] at h10
  have hout := park_triple L hw hn (Edges.outStage L C) R1 S b
    (dialogFlagState L false D I false false H false) (dialogFlagState L false false I false false false false)
    (dialogFlagState_read L hn false D I false false H false).2.2.2.1
    (dialogFlagState_read L hn false false I false false false false).2.2.2.1
    (by simpa only [Edges.outStage, List.append_assoc] using (h10a.seq h8).seq h10)
  have merge_run (s : State) (m : List Bool) :
      run (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ Edges.shared L C)) m s =
        run (genFlagN L ++ renameProgram (sigP L) (Edges.outStage L C)) m s := by
    have shape : genFlagN L ++ renameProgram (sigP L) (Edges.outStage L C) =
        (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) ++
          renameProgram (sigP L) (corners2 L C ++ Edges.shared L C) := by
      simp only [Edges.outStage,rename_append,sigP_zeroFlag L hw hn,List.append_assoc]
    rw [shape,run_append,run_take]
    rw [run_append (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)),run_take]
    simp only [show measurementCount (mergeFlagsN L)=0 from rfl,
      show measurementCount (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L))=0 from rfl,
      List.drop_zero]
    rw [mergeFlagsN_run_eq L hw hn s m]
  have hmerged : Triple (PointDialogBoundary L R1 b (dialogFlagState L false D G false false H false))
      (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ Edges.shared L C))
      (PointDialogBoundary L S b (dialogFlagState L false false I false false false false)) := by
    intro s m hs
    rw [merge_run]
    exact (h9.seq hout) s m hs
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← dh3_10_equal_simp]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := ((((((h3.seq h6).seq hf1).seq h7).seq hu).seq hmerged).seq h12)
  simpa only [finiteProgram,List.append_assoc,dialogFlagState_zero] using h


theorem Edges.shared_counts (L : ControlledPointLayout) (hw : L.Widths) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.shared L (.some hc))=258 ∧ measurementCount (Edges.shared L (.some hc))=256 := by
  have tc : tailCost true (yBit (.some hc)) (exceptionBit (.some hc)) (yBit (-((.some hc) : Point)))=1 := by
    rw [yBit_neg hc]
    cases yBit (.some hc) <;> cases exceptionBit (.some hc) <;> decide
  have hh := affineInputWith_counts (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
    (L.core.poolWire 513) true (yBit (.some hc)) (exceptionBit (.some hc))
    (yBit (-((.some hc) : Point))) (yBit ((.some hc)+(.some hc)))
    L.control (pairPorts L) (pairCode (.some hc)) (pairCode ((.some hc)+(.some hc)))
  simpa only [Edges.shared,pairPorts_length L hw,tc] using hh

theorem shared_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) : GatePhysical (Edges.shared L C) :=
  affineInputWith_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ (shared_nodup L hw hn)

theorem shared_wires (L : ControlledPointLayout) (hw : L.Widths) (C : Point) :
    wires (Edges.shared L C) ⊆ (L.control::yLow L::L.core.generic::L.core.equalNegY::L.doubleSelect::
      L.core.poolWire 513::(pairSrc L++L.dialogPool.take 256)).toFinset := by
  have pp := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  intro q hq
  have hh := affineInputWith_wires (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
    (L.core.poolWire 513) true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C))
    L.control (pairPorts L) (pairCode C) (pairCode (C+C)) hq
  simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
  rcases hh with h|h|h|h|h|h|h
  all_goals first | tauto | (have hm := pp.subset h; change _ at hm; tauto)

def wrapper (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgram L C cy (renameProgram (Wrapper5.U L) Gen))

theorem wrapper_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (wrapper L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  intro s m hi
  have h := finite_spec L hw hn R hc b (renameProgram (Wrapper5.U L) Gen)
    (Wrapper5.genericOK_relabel L hw hc Gen hGen) s m hi
  unfold wrapper
  rw [Square5Placement.pool_relabel_state_eq L (Wrapper5.U L) (Wrapper5.U_pool L hw)
    (Wrapper5.U_outside L hw) _ s m hi.clean h.2.clean]
  exact h

end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component GadgetSubsets
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.OwnDHSubsets
open Arithmetic
attribute [local irreducible] wires
 theorem shared_subset (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  wires (OwnSharedDH.gadget c f g d h x y a1 a2 a3 enD enH cx cy)⊆
   wires (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) := by
  intro q hq
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
   simp [OwnSharedDH.gadget,OwnSharedDH.flipIf,DHGadget.gadget,DHGadget.flipIf,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto
 theorem measured_subset (c f g d h x y a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
  wires (OwnMeasuredDH.gadgetM c f g d h x y a1 a2 a3 enD enH cx cy)⊆
   wires (DHGadget.gadget c f g d h x y a1 a2 a3 enD enH cx cy) := by
  intro q hq
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
   simp [OwnMeasuredDH.gadgetM,DHGadget.gadget,DHGadget.flipIf,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto
end ECDSAAdd.Entrant.OwnDHSubsets

end

section
-- Verified component WrapperProperties
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires run toffoliCount measurementCount
theorem finite_counts (L : ControlledPointLayout) (hw : L.Widths) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (finiteProgram L (.some hc) cy Gen) ≤ 525+toffoliCount Gen ∧
    measurementCount (finiteProgram L (.some hc) cy Gen) ≤ 521+measurementCount Gen := by
  have inp := inputClass_counts L hw hc
  have out := Edges.shared_counts L hw hc
  have zero : toffoliCount (corners2 L (.some hc))=0 ∧ measurementCount (corners2 L (.some hc))=0 := by
    simp only [corners2,toffoliCount_append,measurementCount_append,
      (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2]; decide
  have clear : toffoliCount (clrClear L (.some hc) cy) ≤ 3 ∧ measurementCount (clrClear L (.some hc) cy) ≤ 5 :=
    OwnMeasuredDH.gadgetM_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have restore : toffoliCount (clrRestore L (.some hc) cy) ≤ 4 ∧ measurementCount (clrRestore L (.some hc) cy) ≤ 3 :=
    OwnSharedDH.gadget_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f1 : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have mf : toffoliCount (mergeFlagsN L) = 1 ∧ measurementCount (mergeFlagsN L) = 0 := by
    simp [mergeFlagsN, toffoliCount, measurementCount]
  simp only [finiteProgram,toffoliCount_append,measurementCount_append,renameProgram_counts,
    out.1,out.2,zero.1,zero.2]
  omega


theorem wrapper_counts (L : ControlledPointLayout) (hw:L.Widths) (Gen : Program) {cx cy : Fp}
 (hc:curve.toAffine.Nonsingular cx cy) :
 toffoliCount (wrapper L (.some hc) cy Gen)≤525+toffoliCount Gen ∧
 measurementCount (wrapper L (.some hc) cy Gen)≤521+measurementCount Gen := by
 simpa only [wrapper,renameProgram_counts] using finite_counts L hw (renameProgram (Wrapper5.U L) Gen) hc

theorem clear_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) :
 wires (clrClear L C cy)⊆wires (clrDH L C cy) := OwnDHSubsets.measured_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem restore_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) :
 wires (clrRestore L C cy)⊆wires (clrDH L C cy) := OwnDHSubsets.shared_subset _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem finite_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 wires (finiteProgram L C cy Gen)⊆wires (Edges.finiteProgram L C cy Gen) := by
 intro q hq
 have clear (h:q∈wires (clrClear L C cy)) : q∈wires (clrDH L C cy) := clear_subset L C cy h
 have restore (h:q∈wires (clrRestore L C cy)) : q∈wires (clrDH L C cy) := restore_subset L C cy h
 simp only [finiteProgram,Edges.finiteProgram,wires_append,Finset.mem_union] at hq ⊢
 tauto

theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 wires (wrapper L C cy Gen)⊆wires (Edges.wrapper L C cy Gen) := by
 change wires (renameProgram (Wrapper5.U L) _) ⊆ wires (renameProgram (Wrapper5.U L) _)
 rw [renameProgram_support,renameProgram_support]
 exact Finset.image_subset_image (finite_subset L C cy _)

theorem clear_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (C : Point) (cy : Fp) :
 GatePhysical (clrClear L C cy) := OwnMeasuredDH.gadgetM_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C))
theorem restore_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) (C : Point) (cy : Fp) :
 GatePhysical (clrRestore L C cy) := OwnSharedDH.gadget_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C))
theorem finite_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (C : Point) (cy : Fp) (Gen : Program) (hG:GatePhysical Gen) : GatePhysical (finiteProgram L C cy Gen) := by
 have hp:=Edges.finite_physical L hw hn C cy Gen hG
 have hc:=clear_physical L hw hn C cy
 have hr:=restore_physical L hw hn C cy
 simp only [Edges.finiteProgram,gatePhysical_append] at hp
 simp only [finiteProgram,gatePhysical_append]
 tauto
 theorem wrapper_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (C : Point) (cy : Fp) (Gen : Program) (hG:GatePhysical Gen) : GatePhysical (wrapper L C cy Gen) :=
 gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective _
  (finite_physical L hw hn C cy _ (gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective Gen hG))

theorem finite_slots (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
 gateSlots (finiteProgram L C cy Gen)≤gateSlots (Edges.finiteProgram L C cy Gen)+68 := by
 have hc:gateSlots (clrClear L C cy)≤35:=OwnMeasuredDH.gadgetM_gateSlots _ _ _ _ _ _ _ _ _ _ _ _ _ _
 have hr:gateSlots (clrRestore L C cy)≤33:=OwnSharedDH.gadget_gateSlots _ _ _ _ _ _ _ _ _ _ _ _ _ _
 simp only [finiteProgram,Edges.finiteProgram,gateSlots_append]
 omega
 theorem wrapper_slots (L : ControlledPointLayout) (hw:L.Widths) (C : Point) (cy : Fp) (Gen : Program) :
 gateSlots (wrapper L C cy Gen)≤22904+gateSlots Gen := by
 have old:=Edges.wrapper_slots L hw C cy Gen
 have diff:=finite_slots L C cy (renameProgram (Wrapper5.U L) Gen)
 simp only [wrapper,Edges.wrapper,rename_gateSlots] at old ⊢
 omega
end ECDSAAdd.Entrant.OwnDHWrapper

end

section
-- Verified component FullFrame
namespace ECDSAAdd.Entrant.OwnDHWrapper
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem wrapper_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    wires (wrapper L C cy Gen) ⊆ WrapperOB5.support L :=
 (wrapper_subset L C cy Gen).trans (Edges.wrapper_support L hw hn C cy Gen hG)
private theorem dh3_13_boundary_frame (L : ControlledPointLayout) (P : Program)
    (hP : wires P ⊆ L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q ∉ PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem dh3_13_boundary_work (L : ControlledPointLayout) : L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem dh3_13_work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,ControlledPointLayout.point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- The new support inventory closes the complete work frame, including parity2312. -/
theorem full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen)
    (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} wrapper L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (dh3_13_boundary_work L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := wrapper_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (wrapper_support L hw hn (.some hc) cy Gen hG).trans (WrapperOB5.support_used L hw)
  rw [dh3_13_boundary_frame L _ hsup R _ b s m hi ho q (dh3_13_work_not_point L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end ECDSAAdd.Entrant.OwnDHWrapper

end
