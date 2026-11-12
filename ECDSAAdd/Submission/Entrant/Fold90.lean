import ECDSAAdd.Submission.Entrant.LowAccCarry
import ECDSAAdd.Submission.Entrant.ParkAMany
/-
Provenance for the compact B91 implementation:
The 88-host compiler and arithmetic frame come from promoted submission
64f31ed4-9047-48e1-aa2a-e4ac946ba734. The short checked program-literal
anchors reuse the proof-performance technique of 1fcbdb87-cb36-410b-9f0a-f48b20575965.
Discovery used the intermediate B97 program, including the five-CNOT identity
from cdf6d5e2-5408-4b4e-9d6a-970bb2c11b87 and the seven-repair program
288e1bc0-dc77-4212-aa14-ce114b203c1c. The final body here returns to the
unpatched 88-host loop; those particular CDF/seven/eighth loop repairs are
not retained. Generic state, patch, resource and support lemmas are retained
from the seven-repair proof framework. Two new fold identities and a short
rebuild output-frame proof provide the B91 gain. Public terminal removals
from b566a8f1-1884-42cd-9a7d-f2e9b975ab1e are separately credited in DeadCarry.
-/

section
-- Preserved checked proof component: SixCarryBase
namespace ECDSAAdd.Entrant
open ECDSAAdd Arithmetic
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace SixCarryTrace
def basisStep : Instr → BasisState → BasisState
 | .X t, b => writeBit b t (!b t)
 | .CX a t, b => writeBit b t (b t ^^ b a)
 | .CCX a c t, b => writeBit b t (b t ^^ (b a && b c))
 | .measureX t _ _, b => writeBit b t false

def basisRun : Program → BasisState → BasisState
 | [], b => b
 | i::p,b => basisRun p (basisStep i b)

theorem run_basis (p : Program) (m : List Bool) (s : State) :
 (run p m s).basis = basisRun p s.basis := by
 induction p generalizing m s with
 | nil => rfl
 | cons i p ih => cases i <;> simp [run,basisRun,basisStep,ih,measureAndCorrect]

theorem basisRun_append (p q : Program) (b : BasisState) :
 basisRun (p++q) b = basisRun q (basisRun p b) := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih => simp [basisRun,ih]

def stripPhase : Instr → Instr
 | .measureX q _ _ => .measureX q [] []
 | i => i

theorem basisRun_stripPhase (p : Program) (b : BasisState) :
 basisRun (p.map stripPhase) b = basisRun p b := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih => cases i <;> simp [basisRun,stripPhase,ih,basisStep]


end SixCarryTrace
namespace SixCarryFrame
open SixCarryTrace
def target : Instr → Wire
 | .X q => q
 | .CX _ q => q
 | .CCX _ _ q => q
 | .measureX q _ _ => q

theorem basisStep_preserves (i : Instr) (b : BasisState) (q : Wire) (h : target i ≠ q) :
 basisStep i b q = b q := by
 have hrev := Ne.symm h
 cases i <;> simp_all [target,basisStep,writeBit]

theorem basisRun_preserves (p : Program) (b : BasisState) (q : Wire)
 (h : ∀ i ∈ p, target i ≠ q) : basisRun p b q = b q := by
 induction p generalizing b with
 | nil => rfl
 | cons i p ih =>
  change basisRun p (basisStep i b) q = b q
  rw [ih _ (fun j hj => h j (by simp [hj]))]
  exact basisStep_preserves i b q (h i (by simp))

def prefixState (p : Program) (i : Nat) (b : BasisState) : BasisState := basisRun (p.take i) b

theorem at_succ (p : Program) (i : Nat) (hi : i < p.length) (b : BasisState) :
 prefixState p (i+1) b = basisStep p[i] (prefixState p i b) := by
 simp only [prefixState,List.take_succ_eq_append_getElem hi,basisRun_append,basisRun]

def noWriteBetween (p : Program) (i j : Nat) (q : Wire) : Bool :=
 ((p.drop i).take (j-i)).all (fun ins => decide (target ins ≠ q))

theorem at_between (p : Program) (i j : Nat) (q : Wire) (hij : i ≤ j)
 (hn : noWriteBetween p i j q = true) (b : BasisState) :
 prefixState p j b q = prefixState p i b q := by
 unfold prefixState
 rw [show j = i+(j-i) from by omega,List.take_add,basisRun_append]
 apply basisRun_preserves
 intro ins hins
 exact of_decide_eq_true (List.all_eq_true.mp hn ins hins)

theorem at_full (p : Program) (b : BasisState) : prefixState p p.length b = basisRun p b := by
 simp only [prefixState,List.take_length]


end SixCarryFrame
namespace SixCarryReplace
theorem old_shape_of_lookup (p : Program) (i : Nat) (g : Instr)
 (h : p[i]? = some g) : p = p.take i ++ ([g] ++ p.drop (i+1)) := by
 obtain ⟨hi,hg⟩ := List.getElem?_eq_some_iff.mp h
 have hd := List.drop_eq_getElem_cons hi
 rw [hg] at hd
 exact (List.take_append_drop i p).symm.trans (congrArg (fun q => p.take i ++ q) hd)

end SixCarryReplace
namespace SixCarryReplacement
theorem state_ext {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
 cases s
 cases t
 cases hp
 cases hb
 rfl

end SixCarryReplacement
namespace SixCarrySupport
theorem replacement_support (pre old new post : Program)
 (hs : wires new ⊆ wires (pre ++ (old ++ post))) :
 wires (pre ++ (new ++ post)) ⊆ wires (pre ++ (old ++ post)) := by
 intro w hw
 simp only [wires_append,Finset.mem_union] at hw ⊢
 rcases hw with h | h | h
 · exact Or.inl h
 · have hh:=hs h; simpa only [wires_append,Finset.mem_union] using hh
 · exact Or.inr (Or.inr h)

theorem replacement_physical (pre old new post : Program)
 (hp : GatePhysical (pre ++ (old ++ post))) (hn : GatePhysical new) :
 GatePhysical (pre ++ (new ++ post)) := by
 simp only [gatePhysical_append] at hp ⊢
 exact ⟨hp.1,hn,hp.2.2⟩

end SixCarrySupport
namespace SixCarryResource
theorem slots_append (p q : Program) : Challenge.gateSlots (p++q)=Challenge.gateSlots p+Challenge.gateSlots q := by
 simp [Challenge.gateSlots,List.map_append,List.sum_append]
end SixCarryResource
end ECDSAAdd.Entrant

end

section
-- Preserved checked proof component: SixCarryPatchGeneric
namespace ECDSAAdd.Entrant.SixCarryPatchGeneric
open ECDSAAdd SixCarryReplace
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def patch (p : Program) (i : Nat) (replacement : Program) : Program :=
 p.take i++(replacement++p.drop (i+1))

theorem run_eq (p : Program) (i a b t : Nat) (replacement : Program)
 (hg : p[i]?=some (.CCX a b t)) (hm : measurementCount replacement=0)
 (s : State) (m : List Bool)
 (h : run [.CCX a b t] [] (run (p.take i) (m.take (measurementCount (p.take i))) s)=
      run replacement [] (run (p.take i) (m.take (measurementCount (p.take i))) s)) :
 run p m s=run (patch p i replacement) m s := by
 have shape := old_shape_of_lookup p i (.CCX a b t) hg
 conv_lhs => rw [shape]
 unfold patch
 conv_lhs => rw [run_append]
 conv_rhs => rw [run_append]
 rw [run_append,run_append,hm]
 simpa only [measurementCount,List.take_zero,List.drop_zero] using
  congrArg (run (p.drop (i+1)) (m.drop (measurementCount (p.take i)))) h
end ECDSAAdd.Entrant.SixCarryPatchGeneric

end

section
-- Preserved checked proof component: SixCarryPatchResources
namespace ECDSAAdd.Entrant.SixCarryPatchResources
open ECDSAAdd Challenge SixCarryPatchGeneric SixCarryReplace
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem toffoli (p : Program) (i a b t : Nat) (r : Program)
 (hg : p[i]?=some (.CCX a b t)) (hr : toffoliCount r=0) :
 toffoliCount (patch p i r)+1=toffoliCount p := by
 have h := congrArg toffoliCount (old_shape_of_lookup p i (.CCX a b t) hg)
 have one : toffoliCount [.CCX a b t]=1 := by simp only [toffoliCount]
 simp only [toffoliCount_append,one] at h
 simp only [patch,toffoliCount_append,hr]
 omega

theorem measurements (p : Program) (i a b t : Nat) (r : Program)
 (hg : p[i]?=some (.CCX a b t)) (hr : measurementCount r=0) :
 measurementCount (patch p i r)=measurementCount p := by
 have h := congrArg measurementCount (old_shape_of_lookup p i (.CCX a b t) hg)
 have zero : measurementCount [.CCX a b t]=0 := by simp only [measurementCount]
 simp only [measurementCount_append,zero] at h
 simp only [patch,measurementCount_append,hr]
 omega

theorem slots (p : Program) (i a b t : Nat) (r : Program) (n : Nat)
 (hg : p[i]?=some (.CCX a b t)) (hr : gateSlots r=n+1) :
 gateSlots (patch p i r)=gateSlots p+n := by
 have h := congrArg gateSlots (old_shape_of_lookup p i (.CCX a b t) hg)
 have one : gateSlots [.CCX a b t]=1 := by unfold gateSlots; rfl
 simp only [SixCarryResource.slots_append,one] at h
 simp only [patch,SixCarryResource.slots_append,hr]
 omega
end ECDSAAdd.Entrant.SixCarryPatchResources

end

section
-- Preserved checked proof component: SixCarryPatchPrefix
namespace ECDSAAdd.Entrant.SixCarryPatchPrefix
open ECDSAAdd SixCarryPatchGeneric
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem take_before (p : Program) (j : Nat) (g : Instr) (r : Program) (i : Nat)
 (hg : p[j]?=some g) (hi : i≤j) : (patch p j r).take i=p.take i := by
 have hj := (List.getElem?_eq_some_iff.mp hg).1
 unfold patch
 rw [List.take_append_of_le_length (by rw [List.length_take];omega),List.take_take,Nat.min_eq_left hi]

theorem lookup_before (p : Program) (j : Nat) (g : Instr) (r : Program) (i : Nat)
 (hg : p[j]?=some g) (hi : i<j) : (patch p j r)[i]?=p[i]? := by
 have hj := (List.getElem?_eq_some_iff.mp hg).1
 unfold patch
 rw [List.getElem?_append_left (by rw [List.length_take];omega),List.getElem?_take_of_lt hi]
end ECDSAAdd.Entrant.SixCarryPatchPrefix

end

section
-- Preserved checked proof component: SmallPatchSupport
namespace ECDSAAdd.Entrant.SixCarryPatchSupport
open ECDSAAdd Arithmetic SixCarryPatchGeneric SixCarryReplace
theorem support (p : Program) (i : Nat) (g : Instr) (r : Program)
 (hg : p[i]?=some g) (hr : wires r⊆wires p) : wires (patch p i r)⊆wires p := by
 have hs := old_shape_of_lookup p i g hg
 exact Eq.mp (congrArg (fun p'=>wires (patch p i r)⊆wires p') hs.symm)
  (SixCarrySupport.replacement_support (p.take i) [g] r (p.drop (i+1))
   (Eq.mp (congrArg (fun p'=>wires r⊆wires p') hs) hr))

theorem physical (p : Program) (i : Nat) (g : Instr) (r : Program)
 (hg : p[i]?=some g) (hp : GatePhysical p) (hr : GatePhysical r) : GatePhysical (patch p i r) := by
 have hs := old_shape_of_lookup p i g hg
 exact SixCarrySupport.replacement_physical (p.take i) [g] r (p.drop (i+1))
  (Eq.mp (congrArg GatePhysical hs) hp) hr

end ECDSAAdd.Entrant.SixCarryPatchSupport

end

section
-- Preserved checked proof component: SmallPatchSlots
namespace ECDSAAdd.Entrant.ExtraCarryResourceGeneric
open ECDSAAdd Challenge
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] Challenge.gateSlots

theorem patch_slots_zero (p : Program) (i a b t : Nat) (r : Program)
 (hg : p[i]?=some (.CCX a b t)) (hr : gateSlots r=1) :
 gateSlots (SixCarryPatchGeneric.patch p i r)=gateSlots p := by
 have h := SixCarryPatchResources.slots p i a b t r 0 hg (by simpa only [Nat.zero_add] using hr)
 simpa only [Nat.add_zero] using h

end ECDSAAdd.Entrant.ExtraCarryResourceGeneric

end

section
-- Preserved checked proof component: LocalEFoldTrace
open ECDSAAdd Lean
namespace ECDSAAdd.Entrant.LocalEFoldTrace
open SixCarryTrace SixCarryFrame
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
def chunk0 : Program := [
.CX 4113 4115,
.CX 4113 4116,
.CX 4113 4117,
.CX 4113 4118,
.CX 4113 4119,
.CX 4113 4120,
.CX 4113 4121,
.CX 4113 4122,
.CX 4113 4123,
.CX 4113 4124,
.CX 4113 4125,
.CX 4113 4126,
.CX 4113 4127,
.CX 4113 4128,
.CX 4113 4129,
.CX 4113 4130,
.CX 4113 4131,
.CX 4113 4132,
.CX 4113 4133,
.CX 4113 4134,
.CX 4113 4135,
.CX 4113 4136,
.CX 4113 4137,
.CX 4113 4138,
.CX 4113 4139,
.CX 4113 4140,
.CX 4113 4141,
.CX 4113 4142,
.CX 4113 4143,
.CX 4113 4144,
.CX 4113 4145,
.CX 4113 4146,
.CX 4113 4147,
.CX 4113 4148,
.CX 4113 4149,
.CX 4113 4150,
.CX 4113 4151,
.CX 4113 4152,
.CX 4113 4153,
.CX 4113 4154,
.CX 4113 4155,
.CX 4113 4156,
.CX 4113 4157,
.CX 4113 4158,
.CX 4113 4159,
.CX 4113 4160,
.CX 4113 4161,
.CX 4113 4162,
.CX 4113 4163,
.CX 4113 4164,
.CX 4113 4165,
.CX 4113 4166,
.CX 4113 4167,
.CX 4113 4168,
.CX 4113 4169,
.CX 4113 4170,
.CX 4113 4171,
.CX 4113 4172,
.CX 4113 4173,
.CX 4113 4174,
.CX 4113 4175,
.CX 4113 4176,
.CX 4113 4177,
.CX 4113 4178,
.CX 4113 4179,
.CX 4113 4180,
.CX 4113 4181,
.CX 4113 4182,
.CX 4113 4183,
.CX 4113 4184,
.CX 4113 4185,
.CX 4113 4186,
.CX 4113 4187,
.CX 4113 4188,
.CX 4113 4189,
.CX 4113 4190,
.CX 4113 4191,
.CX 4113 4192,
.CX 4113 4193,
.CX 4113 4194,
.CX 4113 4195,
.CX 4113 4196,
.CX 4113 4197,
.CX 4113 4198,
.CX 4113 4199,
.CX 4113 4200,
.CX 4113 4201,
.CX 4113 4202,
.CX 4113 4203,
.CX 4113 4204,
.CX 4113 4205,
.CX 4113 4206,
.CX 4113 4207,
.CX 4113 4208,
.CX 4113 4209,
.CX 4113 4210,
.CX 4113 4211,
.CX 4113 4212,
.CX 4113 4213,
.CX 4113 4214,
.CX 4113 4215,
.CX 4113 4216,
.CX 4113 4217,
.CX 4113 4218,
.CX 4113 4219,
.CX 4113 4220,
.CX 4113 4221,
.CX 4113 4222,
.CX 4113 4223,
.CX 4113 4224,
.CX 4113 4225,
.CX 4113 4226,
.CX 4113 4227,
.CX 4113 4228,
.CX 4113 4229,
.CX 4113 4230,
.CX 4113 4231,
.CX 4113 4232,
.CX 4113 4233,
.CX 4113 4234,
.CX 4113 4235,
.CX 4113 4236,
.CX 4113 4237,
.CX 4113 4238,
.CX 4113 4239,
.CX 4113 4240,
.CX 4113 4241,
.CX 4113 4242
]
def chunk1 : Program := [
.CX 4113 4371,
.CX 4115 4505,
.CX 4116 4506,
.CX 4117 4507,
.CX 4118 4508,
.CX 4119 4509,
.CX 4120 4510,
.CX 4121 4511,
.CX 4122 4512,
.CX 4123 4513,
.CX 4124 4514,
.CX 4125 4515,
.CX 4126 4516,
.CX 4127 4517,
.CX 4128 4518,
.CX 4129 4519,
.CX 4130 4520,
.CX 4131 4521,
.CX 4132 4522,
.CX 4133 4523,
.CX 4134 4524,
.CX 4135 4525,
.CX 4136 4526,
.CX 4137 4527,
.CX 4138 4528,
.CX 4139 4529,
.CX 4140 4530,
.CX 4141 4531,
.CX 4142 4532,
.CX 4143 4533,
.CX 4144 4534,
.CX 4145 4535,
.CX 4146 4536,
.CX 4147 4537,
.CX 4148 4538,
.CX 4149 4539,
.CX 4150 4540,
.CX 4151 4541,
.CX 4152 4542,
.CX 4153 4543,
.CX 4154 4544,
.CX 4155 4545,
.CX 4156 4546,
.CX 4157 4547,
.CX 4158 4548,
.CX 4159 4549,
.CX 4160 4550,
.CX 4161 4551,
.CX 4162 4552,
.CX 4163 4553,
.CX 4164 4554,
.CX 4165 4555,
.CX 4166 4556,
.CX 4167 4557,
.CX 4168 4558,
.CX 4169 4559,
.CX 4170 4560,
.CX 4171 4561,
.CX 4172 4562,
.CX 4173 4563,
.CX 4174 4564,
.CX 4175 4565,
.CX 4176 4566,
.CX 4177 4567,
.CX 4178 4568,
.CX 4179 4569,
.CX 4180 4570,
.CX 4181 4571,
.CX 4182 4572,
.CX 4183 4573,
.CX 4184 4574,
.CX 4185 4575,
.CX 4186 4576,
.CX 4187 4577,
.CX 4188 4578,
.CX 4189 4579,
.CX 4190 4580,
.CX 4191 4581,
.CX 4192 4582,
.CX 4193 4583,
.CX 4194 4584,
.CX 4195 4585,
.CX 4196 4586,
.CX 4197 4587,
.CX 4198 4588,
.CX 4199 4589,
.CX 4200 4590,
.CX 4201 4591,
.CX 4202 4592,
.CX 4203 4593,
.CX 4204 4594,
.CX 4205 4595,
.CX 4206 4596,
.CX 4207 4597,
.CX 4208 4598,
.CX 4209 4599,
.CX 4210 4600,
.CX 4211 4601,
.CX 4212 4602,
.CX 4213 4603,
.CX 4214 4604,
.CX 4215 4605,
.CX 4216 4606,
.CX 4217 4607,
.CX 4218 4608,
.CX 4219 4609,
.CX 4220 4610,
.CX 4221 4611,
.CX 4222 4612,
.CX 4223 4613,
.CX 4224 4614,
.CX 4225 4615,
.CX 4226 4616,
.CX 4227 4617,
.CX 4228 4618,
.CX 4229 4619,
.CX 4230 4620,
.CX 4231 4621,
.CX 4232 4622,
.CX 4233 4623,
.CX 4234 4624,
.CX 4235 4625,
.CX 4236 4626,
.CX 4237 4627,
.CX 4238 4628,
.CX 4239 4629,
.CX 4240 4630,
.CX 4241 4631
]
def chunk2 : Program := [
.CX 4242 4632,
.CX 4371 4633,
.CX 4372 4634,
.CX 4697 4635,
.CX 4698 4636,
.CX 4699 4637,
.CX 4700 4638,
.CX 4701 4639,
.CX 4702 4640,
.CX 4703 4641,
.CX 4704 4642,
.CX 4705 4643,
.CX 4706 4644,
.CX 4707 4645,
.CX 4708 4646,
.CX 4709 4647,
.CX 4710 4648,
.CX 4711 4649,
.CX 4712 4650,
.CX 4713 4651,
.CX 4714 4652,
.CX 4715 4653,
.CX 4716 4654,
.CX 4717 4655,
.CX 4718 4656,
.CX 4719 4657,
.CX 4720 4658,
.CX 4721 4659,
.CX 4722 4660,
.CX 4723 4661,
.CX 4724 4662,
.CX 4725 4663,
.CX 4115 4511,
.CX 4115 4760,
.CCX 4511 4760 4373,
.CX 4115 4373,
.CX 4115 4760,
.CX 4115 4511,
.CX 4116 4512,
.CX 4116 4373,
.CCX 4512 4373 4374,
.CX 4116 4374,
.CX 4116 4373,
.CX 4116 4512,
.CX 4117 4513,
.CX 4117 4374,
.CCX 4513 4374 4375,
.CX 4117 4375,
.CX 4117 4374,
.CX 4117 4513,
.CX 4118 4514,
.CX 4118 4375,
.CCX 4514 4375 4376,
.CX 4118 4376,
.CX 4118 4375,
.CX 4118 4514,
.CX 4119 4515,
.CX 4119 4376,
.CCX 4515 4376 4377,
.CX 4119 4377,
.CX 4119 4376,
.CX 4119 4515,
.CX 4120 4516,
.CX 4120 4377,
.CCX 4516 4377 4378,
.CX 4120 4378,
.CX 4120 4377,
.CX 4120 4516,
.CX 4121 4517,
.CX 4121 4378,
.CCX 4517 4378 4379,
.CX 4121 4379,
.CX 4121 4378,
.CX 4121 4517,
.CX 4122 4518,
.CX 4122 4379,
.CCX 4518 4379 4380,
.CX 4122 4380,
.CX 4122 4379,
.CX 4122 4518,
.CX 4123 4519,
.CX 4123 4380,
.CCX 4519 4380 4381,
.CX 4123 4381,
.CX 4123 4380,
.CX 4123 4519,
.CX 4124 4520,
.CX 4124 4381,
.CCX 4520 4381 4382,
.CX 4124 4382,
.CX 4124 4381,
.CX 4124 4520,
.CX 4125 4521,
.CX 4125 4382,
.CCX 4521 4382 4383,
.CX 4125 4383,
.CX 4125 4382,
.CX 4125 4521,
.CX 4126 4522,
.CX 4126 4383,
.CCX 4522 4383 4384,
.CX 4126 4384,
.CX 4126 4383,
.CX 4126 4522,
.CX 4127 4523,
.CX 4127 4384,
.CCX 4523 4384 4385,
.CX 4127 4385,
.CX 4127 4384,
.CX 4127 4523,
.CX 4128 4524,
.CX 4128 4385,
.CCX 4524 4385 4386,
.CX 4128 4386,
.CX 4128 4385,
.CX 4128 4524,
.CX 4129 4525,
.CX 4129 4386,
.CCX 4525 4386 4387,
.CX 4129 4387,
.CX 4129 4386,
.CX 4129 4525,
.CX 4130 4526,
.CX 4130 4387,
.CCX 4526 4387 4388,
.CX 4130 4388,
.CX 4130 4387,
.CX 4130 4526
]
def chunk3 : Program := [
.CX 4131 4527,
.CX 4131 4388,
.CCX 4527 4388 4389,
.CX 4131 4389,
.CX 4131 4388,
.CX 4131 4527,
.CX 4132 4528,
.CX 4132 4389,
.CCX 4528 4389 4390,
.CX 4132 4390,
.CX 4132 4389,
.CX 4132 4528,
.CX 4133 4529,
.CX 4133 4390,
.CCX 4529 4390 4391,
.CX 4133 4391,
.CX 4133 4390,
.CX 4133 4529,
.CX 4134 4530,
.CX 4134 4391,
.CCX 4530 4391 4392,
.CX 4134 4392,
.CX 4134 4391,
.CX 4134 4530,
.CX 4135 4531,
.CX 4135 4392,
.CCX 4531 4392 4393,
.CX 4135 4393,
.CX 4135 4392,
.CX 4135 4531,
.CX 4136 4532,
.CX 4136 4393,
.CCX 4532 4393 4394,
.CX 4136 4394,
.CX 4136 4393,
.CX 4136 4532,
.CX 4137 4533,
.CX 4137 4394,
.CCX 4533 4394 4395,
.CX 4137 4395,
.CX 4137 4394,
.CX 4137 4533,
.CX 4138 4534,
.CX 4138 4395,
.CCX 4534 4395 4396,
.CX 4138 4396,
.CX 4138 4395,
.CX 4138 4534,
.CX 4139 4535,
.CX 4139 4396,
.CCX 4535 4396 4397,
.CX 4139 4397,
.CX 4139 4396,
.CX 4139 4535,
.CX 4140 4536,
.CX 4140 4397,
.CCX 4536 4397 4398,
.CX 4140 4398,
.CX 4140 4397,
.CX 4140 4536,
.CX 4141 4537,
.CX 4141 4398,
.CCX 4537 4398 4399,
.CX 4141 4399,
.CX 4141 4398,
.CX 4141 4537,
.CX 4142 4538,
.CX 4142 4399,
.CCX 4538 4399 4400,
.CX 4142 4400,
.CX 4142 4399,
.CX 4142 4538,
.CX 4143 4539,
.CX 4143 4400,
.CCX 4539 4400 4401,
.CX 4143 4401,
.CX 4143 4400,
.CX 4143 4539,
.CX 4144 4540,
.CX 4144 4401,
.CCX 4540 4401 4402,
.CX 4144 4402,
.CX 4144 4401,
.CX 4144 4540,
.CX 4145 4541,
.CX 4145 4402,
.CCX 4541 4402 4403,
.CX 4145 4403,
.CX 4145 4402,
.CX 4145 4541,
.CX 4146 4542,
.CX 4146 4403,
.CCX 4542 4403 4404,
.CX 4146 4404,
.CX 4146 4403,
.CX 4146 4542,
.CX 4147 4543,
.CX 4147 4404,
.CCX 4543 4404 4405,
.CX 4147 4405,
.CX 4147 4404,
.CX 4147 4543,
.CX 4148 4544,
.CX 4148 4405,
.CCX 4544 4405 4406,
.CX 4148 4406,
.CX 4148 4405,
.CX 4148 4544,
.CX 4149 4545,
.CX 4149 4406,
.CCX 4545 4406 4407,
.CX 4149 4407,
.CX 4149 4406,
.CX 4149 4545,
.CX 4150 4546,
.CX 4150 4407,
.CCX 4546 4407 4408,
.CX 4150 4408,
.CX 4150 4407,
.CX 4150 4546,
.CX 4151 4547,
.CX 4151 4408,
.CCX 4547 4408 4409,
.CX 4151 4409,
.CX 4151 4408,
.CX 4151 4547,
.CX 4152 4548,
.CX 4152 4409
]
def chunk4 : Program := [
.CCX 4548 4409 4410,
.CX 4152 4410,
.CX 4152 4409,
.CX 4152 4548,
.CX 4153 4549,
.CX 4153 4410,
.CCX 4549 4410 4411,
.CX 4153 4411,
.CX 4153 4410,
.CX 4153 4549,
.CX 4154 4550,
.CX 4154 4411,
.CCX 4550 4411 4412,
.CX 4154 4412,
.CX 4154 4411,
.CX 4154 4550,
.CX 4155 4551,
.CX 4155 4412,
.CCX 4551 4412 4413,
.CX 4155 4413,
.CX 4155 4412,
.CX 4155 4551,
.CX 4156 4552,
.CX 4156 4413,
.CCX 4552 4413 4414,
.CX 4156 4414,
.CX 4156 4413,
.CX 4156 4552,
.CX 4157 4553,
.CX 4157 4414,
.CCX 4553 4414 4415,
.CX 4157 4415,
.CX 4157 4414,
.CX 4157 4553,
.CX 4158 4554,
.CX 4158 4415,
.CCX 4554 4415 4416,
.CX 4158 4416,
.CX 4158 4415,
.CX 4158 4554,
.CX 4159 4555,
.CX 4159 4416,
.CCX 4555 4416 4417,
.CX 4159 4417,
.CX 4159 4416,
.CX 4159 4555,
.CX 4160 4556,
.CX 4160 4417,
.CCX 4556 4417 4418,
.CX 4160 4418,
.CX 4160 4417,
.CX 4160 4556,
.CX 4161 4557,
.CX 4161 4418,
.CCX 4557 4418 4419,
.CX 4161 4419,
.CX 4161 4418,
.CX 4161 4557,
.CX 4162 4558,
.CX 4162 4419,
.CCX 4558 4419 4420,
.CX 4162 4420,
.CX 4162 4419,
.CX 4162 4558,
.CX 4163 4559,
.CX 4163 4420,
.CCX 4559 4420 4421,
.CX 4163 4421,
.CX 4163 4420,
.CX 4163 4559,
.CX 4164 4560,
.CX 4164 4421,
.CCX 4560 4421 4422,
.CX 4164 4422,
.CX 4164 4421,
.CX 4164 4560,
.CX 4165 4561,
.CX 4165 4422,
.CCX 4561 4422 4423,
.CX 4165 4423,
.CX 4165 4422,
.CX 4165 4561,
.CX 4166 4562,
.CX 4166 4423,
.CCX 4562 4423 4424,
.CX 4166 4424,
.CX 4166 4423,
.CX 4166 4562,
.CX 4167 4563,
.CX 4167 4424,
.CCX 4563 4424 4425,
.CX 4167 4425,
.CX 4167 4424,
.CX 4167 4563,
.CX 4168 4564,
.CX 4168 4425,
.CCX 4564 4425 4426,
.CX 4168 4426,
.CX 4168 4425,
.CX 4168 4564,
.CX 4169 4565,
.CX 4169 4426,
.CCX 4565 4426 4427,
.CX 4169 4427,
.CX 4169 4426,
.CX 4169 4565,
.CX 4170 4566,
.CX 4170 4427,
.CCX 4566 4427 4428,
.CX 4170 4428,
.CX 4170 4427,
.CX 4170 4566,
.CX 4171 4567,
.CX 4171 4428,
.CCX 4567 4428 4429,
.CX 4171 4429,
.CX 4171 4428,
.CX 4171 4567,
.CX 4172 4568,
.CX 4172 4429,
.CCX 4568 4429 4430,
.CX 4172 4430,
.CX 4172 4429,
.CX 4172 4568,
.CX 4173 4569,
.CX 4173 4430,
.CCX 4569 4430 4431,
.CX 4173 4431
]
def chunk5 : Program := [
.CX 4173 4430,
.CX 4173 4569,
.CX 4174 4570,
.CX 4174 4431,
.CCX 4570 4431 4432,
.CX 4174 4432,
.CX 4174 4431,
.CX 4174 4570,
.CX 4175 4571,
.CX 4175 4432,
.CCX 4571 4432 4433,
.CX 4175 4433,
.CX 4175 4432,
.CX 4175 4571,
.CX 4176 4572,
.CX 4176 4433,
.CCX 4572 4433 4434,
.CX 4176 4434,
.CX 4176 4433,
.CX 4176 4572,
.CX 4177 4573,
.CX 4177 4434,
.CCX 4573 4434 4435,
.CX 4177 4435,
.CX 4177 4434,
.CX 4177 4573,
.CX 4178 4574,
.CX 4178 4435,
.CCX 4574 4435 4436,
.CX 4178 4436,
.CX 4178 4435,
.CX 4178 4574,
.CX 4179 4575,
.CX 4179 4436,
.CCX 4575 4436 4437,
.CX 4179 4437,
.CX 4179 4436,
.CX 4179 4575,
.CX 4180 4576,
.CX 4180 4437,
.CCX 4576 4437 4438,
.CX 4180 4438,
.CX 4180 4437,
.CX 4180 4576,
.CX 4181 4577,
.CX 4181 4438,
.CCX 4577 4438 4439,
.CX 4181 4439,
.CX 4181 4438,
.CX 4181 4577,
.CX 4182 4578,
.CX 4182 4439,
.CCX 4578 4439 4440,
.CX 4182 4440,
.CX 4182 4439,
.CX 4182 4578,
.CX 4183 4579,
.CX 4183 4440,
.CCX 4579 4440 4441,
.CX 4183 4441,
.CX 4183 4440,
.CX 4183 4579,
.CX 4184 4580,
.CX 4184 4441,
.CCX 4580 4441 4442,
.CX 4184 4442,
.CX 4184 4441,
.CX 4184 4580,
.CX 4185 4581,
.CX 4185 4442,
.CCX 4581 4442 4443,
.CX 4185 4443,
.CX 4185 4442,
.CX 4185 4581,
.CX 4186 4582,
.CX 4186 4443,
.CCX 4582 4443 4444,
.CX 4186 4444,
.CX 4186 4443,
.CX 4186 4582,
.CX 4187 4583,
.CX 4187 4444,
.CCX 4583 4444 4445,
.CX 4187 4445,
.CX 4187 4444,
.CX 4187 4583,
.CX 4188 4584,
.CX 4188 4445,
.CCX 4584 4445 4446,
.CX 4188 4446,
.CX 4188 4445,
.CX 4188 4584,
.CX 4189 4585,
.CX 4189 4446,
.CCX 4585 4446 4447,
.CX 4189 4447,
.CX 4189 4446,
.CX 4189 4585,
.CX 4190 4586,
.CX 4190 4447,
.CCX 4586 4447 4448,
.CX 4190 4448,
.CX 4190 4447,
.CX 4190 4586,
.CX 4191 4587,
.CX 4191 4448,
.CCX 4587 4448 4449,
.CX 4191 4449,
.CX 4191 4448,
.CX 4191 4587,
.CX 4192 4588,
.CX 4192 4449,
.CCX 4588 4449 4450,
.CX 4192 4450,
.CX 4192 4449,
.CX 4192 4588,
.CX 4193 4589,
.CX 4193 4450,
.CCX 4589 4450 4451,
.CX 4193 4451,
.CX 4193 4450,
.CX 4193 4589,
.CX 4194 4590,
.CX 4194 4451,
.CCX 4590 4451 4452,
.CX 4194 4452,
.CX 4194 4451,
.CX 4194 4590
]
def chunk6 : Program := [
.CX 4195 4591,
.CX 4195 4452,
.CCX 4591 4452 4453,
.CX 4195 4453,
.CX 4195 4452,
.CX 4195 4591,
.CX 4196 4592,
.CX 4196 4453,
.CCX 4592 4453 4454,
.CX 4196 4454,
.CX 4196 4453,
.CX 4196 4592,
.CX 4197 4593,
.CX 4197 4454,
.CCX 4593 4454 4455,
.CX 4197 4455,
.CX 4197 4454,
.CX 4197 4593,
.CX 4198 4594,
.CX 4198 4455,
.CCX 4594 4455 4456,
.CX 4198 4456,
.CX 4198 4455,
.CX 4198 4594,
.CX 4199 4595,
.CX 4199 4456,
.CCX 4595 4456 4457,
.CX 4199 4457,
.CX 4199 4456,
.CX 4199 4595,
.CX 4200 4596,
.CX 4200 4457,
.CCX 4596 4457 4458,
.CX 4200 4458,
.CX 4200 4457,
.CX 4200 4596,
.CX 4201 4597,
.CX 4201 4458,
.CCX 4597 4458 4459,
.CX 4201 4459,
.CX 4201 4458,
.CX 4201 4597,
.CX 4202 4598,
.CX 4202 4459,
.CCX 4598 4459 4460,
.CX 4202 4460,
.CX 4202 4459,
.CX 4202 4598,
.CX 4203 4599,
.CX 4203 4460,
.CCX 4599 4460 4461,
.CX 4203 4461,
.CX 4203 4460,
.CX 4203 4599,
.CX 4204 4600,
.CX 4204 4461,
.CCX 4600 4461 4462,
.CX 4204 4462,
.CX 4204 4461,
.CX 4204 4600,
.CX 4205 4601,
.CX 4205 4462,
.CCX 4601 4462 4463,
.CX 4205 4463,
.CX 4205 4462,
.CX 4205 4601,
.CX 4206 4602,
.CX 4206 4463,
.CCX 4602 4463 4464,
.CX 4206 4464,
.CX 4206 4463,
.CX 4206 4602,
.CX 4207 4603,
.CX 4207 4464,
.CCX 4603 4464 4465,
.CX 4207 4465,
.CX 4207 4464,
.CX 4207 4603,
.CX 4208 4604,
.CX 4208 4465,
.CCX 4604 4465 4466,
.CX 4208 4466,
.CX 4208 4465,
.CX 4208 4604,
.CX 4209 4605,
.CX 4209 4466,
.CCX 4605 4466 4467,
.CX 4209 4467,
.CX 4209 4466,
.CX 4209 4605,
.CX 4210 4606,
.CX 4210 4467,
.CCX 4606 4467 4468,
.CX 4210 4468,
.CX 4210 4467,
.CX 4210 4606,
.CX 4211 4607,
.CX 4211 4468,
.CCX 4607 4468 4469,
.CX 4211 4469,
.CX 4211 4468,
.CX 4211 4607,
.CX 4212 4608,
.CX 4212 4469,
.CCX 4608 4469 4470,
.CX 4212 4470,
.CX 4212 4469,
.CX 4212 4608,
.CX 4213 4609,
.CX 4213 4470,
.CCX 4609 4470 4471,
.CX 4213 4471,
.CX 4213 4470,
.CX 4213 4609,
.CX 4214 4610,
.CX 4214 4471,
.CCX 4610 4471 4472,
.CX 4214 4472,
.CX 4214 4471,
.CX 4214 4610,
.CX 4215 4611,
.CX 4215 4472,
.CCX 4611 4472 4473,
.CX 4215 4473,
.CX 4215 4472,
.CX 4215 4611,
.CX 4216 4612,
.CX 4216 4473
]
def chunk7 : Program := [
.CCX 4612 4473 4474,
.CX 4216 4474,
.CX 4216 4473,
.CX 4216 4612,
.CX 4217 4613,
.CX 4217 4474,
.CCX 4613 4474 4475,
.CX 4217 4475,
.CX 4217 4474,
.CX 4217 4613,
.CX 4218 4614,
.CX 4218 4475,
.CCX 4614 4475 4476,
.CX 4218 4476,
.CX 4218 4475,
.CX 4218 4614,
.CX 4219 4615,
.CX 4219 4476,
.CCX 4615 4476 4477,
.CX 4219 4477,
.CX 4219 4476,
.CX 4219 4615,
.CX 4220 4616,
.CX 4220 4477,
.CCX 4616 4477 4478,
.CX 4220 4478,
.CX 4220 4477,
.CX 4220 4616,
.CX 4221 4617,
.CX 4221 4478,
.CCX 4617 4478 4479,
.CX 4221 4479,
.CX 4221 4478,
.CX 4221 4617,
.CX 4222 4618,
.CX 4222 4479,
.CCX 4618 4479 4480,
.CX 4222 4480,
.CX 4222 4479,
.CX 4222 4618,
.CX 4223 4619,
.CX 4223 4480,
.CCX 4619 4480 4481,
.CX 4223 4481,
.CX 4223 4480,
.CX 4223 4619,
.CX 4224 4620,
.CX 4224 4481,
.CCX 4620 4481 4482,
.CX 4224 4482,
.CX 4224 4481,
.CX 4224 4620,
.CX 4225 4621,
.CX 4225 4482,
.CCX 4621 4482 4483,
.CX 4225 4483,
.CX 4225 4482,
.CX 4225 4621,
.CX 4226 4622,
.CX 4226 4483,
.CCX 4622 4483 4484,
.CX 4226 4484,
.CX 4226 4483,
.CX 4226 4622,
.CX 4227 4623,
.CX 4227 4484,
.CCX 4623 4484 4485,
.CX 4227 4485,
.CX 4227 4484,
.CX 4227 4623,
.CX 4228 4624,
.CX 4228 4485,
.CCX 4624 4485 4486,
.CX 4228 4486,
.CX 4228 4485,
.CX 4228 4624,
.CX 4229 4625,
.CX 4229 4486,
.CCX 4625 4486 4487,
.CX 4229 4487,
.CX 4229 4486,
.CX 4229 4625,
.CX 4230 4626,
.CX 4230 4487,
.CCX 4626 4487 4488,
.CX 4230 4488,
.CX 4230 4487,
.CX 4230 4626,
.CX 4231 4627,
.CX 4231 4488,
.CCX 4627 4488 4489,
.CX 4231 4489,
.CX 4231 4488,
.CX 4231 4627,
.CX 4232 4628,
.CX 4232 4489,
.CCX 4628 4489 4490,
.CX 4232 4490,
.CX 4232 4489,
.CX 4232 4628,
.CX 4233 4629,
.CX 4233 4490,
.CCX 4629 4490 4491,
.CX 4233 4491,
.CX 4233 4490,
.CX 4233 4629,
.CX 4234 4630,
.CX 4234 4491,
.CCX 4630 4491 4492,
.CX 4234 4492,
.CX 4234 4491,
.CX 4234 4630,
.CX 4235 4631,
.CX 4235 4492,
.CCX 4631 4492 4493,
.CX 4235 4493,
.CX 4235 4492,
.CX 4235 4631,
.CX 4236 4632,
.CX 4236 4493,
.CCX 4632 4493 4494,
.CX 4236 4494,
.CX 4236 4493,
.CX 4236 4632,
.CX 4237 4633,
.CX 4237 4494,
.CCX 4633 4494 4495,
.CX 4237 4495
]
def chunk8 : Program := [
.CX 4237 4494,
.CX 4237 4633,
.CX 4238 4634,
.CX 4238 4495,
.CCX 4634 4495 4496,
.CX 4238 4496,
.CX 4238 4495,
.CX 4238 4634,
.CX 4239 4635,
.CX 4239 4496,
.CCX 4635 4496 4497,
.CX 4239 4497,
.CX 4239 4496,
.CX 4239 4635,
.CX 4240 4636,
.CX 4240 4497,
.CCX 4636 4497 4498,
.CX 4240 4498,
.CX 4240 4497,
.CX 4240 4636,
.CX 4241 4637,
.CX 4241 4498,
.CCX 4637 4498 4499,
.CX 4241 4499,
.CX 4241 4498,
.CX 4241 4637,
.CX 4242 4638,
.CX 4242 4499,
.CCX 4638 4499 4500,
.CX 4242 4500,
.CX 4242 4499,
.CX 4242 4638,
.CX 4371 4639,
.CX 4371 4500,
.CCX 4639 4500 4764,
.CX 4371 4764,
.CX 4371 4500,
.CX 4371 4639,
.CX 4372 4640,
.CX 4372 4764,
.CCX 4640 4764 4765,
.CX 4372 4765,
.CX 4372 4764,
.CX 4372 4640,
.CX 4697 4641,
.CX 4765 4641,
.measureX 4765 [] [.CZ 4372 4640,.CZ 4372 4764,.CZ 4640 4764],
.CX 4372 4640,
.CX 4764 4640,
.measureX 4764 [] [.CZ 4371 4639,.CZ 4371 4500,.CZ 4639 4500],
.CX 4371 4639,
.CX 4500 4639,
.measureX 4500 [] [.CZ 4242 4638,.CZ 4242 4499,.CZ 4638 4499],
.CX 4242 4638,
.CX 4499 4638,
.measureX 4499 [] [.CZ 4241 4637,.CZ 4241 4498,.CZ 4637 4498],
.CX 4241 4637,
.CX 4498 4637,
.measureX 4498 [] [.CZ 4240 4636,.CZ 4240 4497,.CZ 4636 4497],
.CX 4240 4636,
.CX 4497 4636,
.measureX 4497 [] [.CZ 4239 4635,.CZ 4239 4496,.CZ 4635 4496],
.CX 4239 4635,
.CX 4496 4635,
.measureX 4496 [] [.CZ 4238 4634,.CZ 4238 4495,.CZ 4634 4495],
.CX 4238 4634,
.CX 4495 4634,
.measureX 4495 [] [.CZ 4237 4633,.CZ 4237 4494,.CZ 4633 4494],
.CX 4237 4633,
.CX 4494 4633,
.measureX 4494 [] [.CZ 4236 4632,.CZ 4236 4493,.CZ 4632 4493],
.CX 4236 4632,
.CX 4493 4632,
.measureX 4493 [] [.CZ 4235 4631,.CZ 4235 4492,.CZ 4631 4492],
.CX 4235 4631,
.CX 4492 4631,
.measureX 4492 [] [.CZ 4234 4630,.CZ 4234 4491,.CZ 4630 4491],
.CX 4234 4630,
.CX 4491 4630,
.measureX 4491 [] [.CZ 4233 4629,.CZ 4233 4490,.CZ 4629 4490],
.CX 4233 4629,
.CX 4490 4629,
.measureX 4490 [] [.CZ 4232 4628,.CZ 4232 4489,.CZ 4628 4489],
.CX 4232 4628,
.CX 4489 4628,
.measureX 4489 [] [.CZ 4231 4627,.CZ 4231 4488,.CZ 4627 4488],
.CX 4231 4627,
.CX 4488 4627,
.measureX 4488 [] [.CZ 4230 4626,.CZ 4230 4487,.CZ 4626 4487],
.CX 4230 4626,
.CX 4487 4626,
.measureX 4487 [] [.CZ 4229 4625,.CZ 4229 4486,.CZ 4625 4486],
.CX 4229 4625,
.CX 4486 4625,
.measureX 4486 [] [.CZ 4228 4624,.CZ 4228 4485,.CZ 4624 4485],
.CX 4228 4624,
.CX 4485 4624,
.measureX 4485 [] [.CZ 4227 4623,.CZ 4227 4484,.CZ 4623 4484],
.CX 4227 4623,
.CX 4484 4623,
.measureX 4484 [] [.CZ 4226 4622,.CZ 4226 4483,.CZ 4622 4483],
.CX 4226 4622,
.CX 4483 4622,
.measureX 4483 [] [.CZ 4225 4621,.CZ 4225 4482,.CZ 4621 4482],
.CX 4225 4621,
.CX 4482 4621,
.measureX 4482 [] [.CZ 4224 4620,.CZ 4224 4481,.CZ 4620 4481],
.CX 4224 4620,
.CX 4481 4620,
.measureX 4481 [] [.CZ 4223 4619,.CZ 4223 4480,.CZ 4619 4480],
.CX 4223 4619,
.CX 4480 4619,
.measureX 4480 [] [.CZ 4222 4618,.CZ 4222 4479,.CZ 4618 4479],
.CX 4222 4618,
.CX 4479 4618,
.measureX 4479 [] [.CZ 4221 4617,.CZ 4221 4478,.CZ 4617 4478],
.CX 4221 4617,
.CX 4478 4617,
.measureX 4478 [] [.CZ 4220 4616,.CZ 4220 4477,.CZ 4616 4477],
.CX 4220 4616,
.CX 4477 4616,
.measureX 4477 [] [.CZ 4219 4615,.CZ 4219 4476,.CZ 4615 4476],
.CX 4219 4615,
.CX 4476 4615,
.measureX 4476 [] [.CZ 4218 4614,.CZ 4218 4475,.CZ 4614 4475],
.CX 4218 4614,
.CX 4475 4614,
.measureX 4475 [] [.CZ 4217 4613,.CZ 4217 4474,.CZ 4613 4474]
]
def chunk9 : Program := [
.CX 4217 4613,
.CX 4474 4613,
.measureX 4474 [] [.CZ 4216 4612,.CZ 4216 4473,.CZ 4612 4473],
.CX 4216 4612,
.CX 4473 4612,
.measureX 4473 [] [.CZ 4215 4611,.CZ 4215 4472,.CZ 4611 4472],
.CX 4215 4611,
.CX 4472 4611,
.measureX 4472 [] [.CZ 4214 4610,.CZ 4214 4471,.CZ 4610 4471],
.CX 4214 4610,
.CX 4471 4610,
.measureX 4471 [] [.CZ 4213 4609,.CZ 4213 4470,.CZ 4609 4470],
.CX 4213 4609,
.CX 4470 4609,
.measureX 4470 [] [.CZ 4212 4608,.CZ 4212 4469,.CZ 4608 4469],
.CX 4212 4608,
.CX 4469 4608,
.measureX 4469 [] [.CZ 4211 4607,.CZ 4211 4468,.CZ 4607 4468],
.CX 4211 4607,
.CX 4468 4607,
.measureX 4468 [] [.CZ 4210 4606,.CZ 4210 4467,.CZ 4606 4467],
.CX 4210 4606,
.CX 4467 4606,
.measureX 4467 [] [.CZ 4209 4605,.CZ 4209 4466,.CZ 4605 4466],
.CX 4209 4605,
.CX 4466 4605,
.measureX 4466 [] [.CZ 4208 4604,.CZ 4208 4465,.CZ 4604 4465],
.CX 4208 4604,
.CX 4465 4604,
.measureX 4465 [] [.CZ 4207 4603,.CZ 4207 4464,.CZ 4603 4464],
.CX 4207 4603,
.CX 4464 4603,
.measureX 4464 [] [.CZ 4206 4602,.CZ 4206 4463,.CZ 4602 4463],
.CX 4206 4602,
.CX 4463 4602,
.measureX 4463 [] [.CZ 4205 4601,.CZ 4205 4462,.CZ 4601 4462],
.CX 4205 4601,
.CX 4462 4601,
.measureX 4462 [] [.CZ 4204 4600,.CZ 4204 4461,.CZ 4600 4461],
.CX 4204 4600,
.CX 4461 4600,
.measureX 4461 [] [.CZ 4203 4599,.CZ 4203 4460,.CZ 4599 4460],
.CX 4203 4599,
.CX 4460 4599,
.measureX 4460 [] [.CZ 4202 4598,.CZ 4202 4459,.CZ 4598 4459],
.CX 4202 4598,
.CX 4459 4598,
.measureX 4459 [] [.CZ 4201 4597,.CZ 4201 4458,.CZ 4597 4458],
.CX 4201 4597,
.CX 4458 4597,
.measureX 4458 [] [.CZ 4200 4596,.CZ 4200 4457,.CZ 4596 4457],
.CX 4200 4596,
.CX 4457 4596,
.measureX 4457 [] [.CZ 4199 4595,.CZ 4199 4456,.CZ 4595 4456],
.CX 4199 4595,
.CX 4456 4595,
.measureX 4456 [] [.CZ 4198 4594,.CZ 4198 4455,.CZ 4594 4455],
.CX 4198 4594,
.CX 4455 4594,
.measureX 4455 [] [.CZ 4197 4593,.CZ 4197 4454,.CZ 4593 4454],
.CX 4197 4593,
.CX 4454 4593,
.measureX 4454 [] [.CZ 4196 4592,.CZ 4196 4453,.CZ 4592 4453],
.CX 4196 4592,
.CX 4453 4592,
.measureX 4453 [] [.CZ 4195 4591,.CZ 4195 4452,.CZ 4591 4452],
.CX 4195 4591,
.CX 4452 4591,
.measureX 4452 [] [.CZ 4194 4590,.CZ 4194 4451,.CZ 4590 4451],
.CX 4194 4590,
.CX 4451 4590,
.measureX 4451 [] [.CZ 4193 4589,.CZ 4193 4450,.CZ 4589 4450],
.CX 4193 4589,
.CX 4450 4589,
.measureX 4450 [] [.CZ 4192 4588,.CZ 4192 4449,.CZ 4588 4449],
.CX 4192 4588,
.CX 4449 4588,
.measureX 4449 [] [.CZ 4191 4587,.CZ 4191 4448,.CZ 4587 4448],
.CX 4191 4587,
.CX 4448 4587,
.measureX 4448 [] [.CZ 4190 4586,.CZ 4190 4447,.CZ 4586 4447],
.CX 4190 4586,
.CX 4447 4586,
.measureX 4447 [] [.CZ 4189 4585,.CZ 4189 4446,.CZ 4585 4446],
.CX 4189 4585,
.CX 4446 4585,
.measureX 4446 [] [.CZ 4188 4584,.CZ 4188 4445,.CZ 4584 4445],
.CX 4188 4584,
.CX 4445 4584,
.measureX 4445 [] [.CZ 4187 4583,.CZ 4187 4444,.CZ 4583 4444],
.CX 4187 4583,
.CX 4444 4583,
.measureX 4444 [] [.CZ 4186 4582,.CZ 4186 4443,.CZ 4582 4443],
.CX 4186 4582,
.CX 4443 4582,
.measureX 4443 [] [.CZ 4185 4581,.CZ 4185 4442,.CZ 4581 4442],
.CX 4185 4581,
.CX 4442 4581,
.measureX 4442 [] [.CZ 4184 4580,.CZ 4184 4441,.CZ 4580 4441],
.CX 4184 4580,
.CX 4441 4580,
.measureX 4441 [] [.CZ 4183 4579,.CZ 4183 4440,.CZ 4579 4440],
.CX 4183 4579,
.CX 4440 4579,
.measureX 4440 [] [.CZ 4182 4578,.CZ 4182 4439,.CZ 4578 4439],
.CX 4182 4578,
.CX 4439 4578,
.measureX 4439 [] [.CZ 4181 4577,.CZ 4181 4438,.CZ 4577 4438],
.CX 4181 4577,
.CX 4438 4577,
.measureX 4438 [] [.CZ 4180 4576,.CZ 4180 4437,.CZ 4576 4437],
.CX 4180 4576,
.CX 4437 4576,
.measureX 4437 [] [.CZ 4179 4575,.CZ 4179 4436,.CZ 4575 4436],
.CX 4179 4575,
.CX 4436 4575,
.measureX 4436 [] [.CZ 4178 4574,.CZ 4178 4435,.CZ 4574 4435],
.CX 4178 4574,
.CX 4435 4574,
.measureX 4435 [] [.CZ 4177 4573,.CZ 4177 4434,.CZ 4573 4434],
.CX 4177 4573,
.CX 4434 4573,
.measureX 4434 [] [.CZ 4176 4572,.CZ 4176 4433,.CZ 4572 4433],
.CX 4176 4572,
.CX 4433 4572,
.measureX 4433 [] [.CZ 4175 4571,.CZ 4175 4432,.CZ 4571 4432],
.CX 4175 4571,
.CX 4432 4571
]
def chunk10 : Program := [
.measureX 4432 [] [.CZ 4174 4570,.CZ 4174 4431,.CZ 4570 4431],
.CX 4174 4570,
.CX 4431 4570,
.measureX 4431 [] [.CZ 4173 4569,.CZ 4173 4430,.CZ 4569 4430],
.CX 4173 4569,
.CX 4430 4569,
.measureX 4430 [] [.CZ 4172 4568,.CZ 4172 4429,.CZ 4568 4429],
.CX 4172 4568,
.CX 4429 4568,
.measureX 4429 [] [.CZ 4171 4567,.CZ 4171 4428,.CZ 4567 4428],
.CX 4171 4567,
.CX 4428 4567,
.measureX 4428 [] [.CZ 4170 4566,.CZ 4170 4427,.CZ 4566 4427],
.CX 4170 4566,
.CX 4427 4566,
.measureX 4427 [] [.CZ 4169 4565,.CZ 4169 4426,.CZ 4565 4426],
.CX 4169 4565,
.CX 4426 4565,
.measureX 4426 [] [.CZ 4168 4564,.CZ 4168 4425,.CZ 4564 4425],
.CX 4168 4564,
.CX 4425 4564,
.measureX 4425 [] [.CZ 4167 4563,.CZ 4167 4424,.CZ 4563 4424],
.CX 4167 4563,
.CX 4424 4563,
.measureX 4424 [] [.CZ 4166 4562,.CZ 4166 4423,.CZ 4562 4423],
.CX 4166 4562,
.CX 4423 4562,
.measureX 4423 [] [.CZ 4165 4561,.CZ 4165 4422,.CZ 4561 4422],
.CX 4165 4561,
.CX 4422 4561,
.measureX 4422 [] [.CZ 4164 4560,.CZ 4164 4421,.CZ 4560 4421],
.CX 4164 4560,
.CX 4421 4560,
.measureX 4421 [] [.CZ 4163 4559,.CZ 4163 4420,.CZ 4559 4420],
.CX 4163 4559,
.CX 4420 4559,
.measureX 4420 [] [.CZ 4162 4558,.CZ 4162 4419,.CZ 4558 4419],
.CX 4162 4558,
.CX 4419 4558,
.measureX 4419 [] [.CZ 4161 4557,.CZ 4161 4418,.CZ 4557 4418],
.CX 4161 4557,
.CX 4418 4557,
.measureX 4418 [] [.CZ 4160 4556,.CZ 4160 4417,.CZ 4556 4417],
.CX 4160 4556,
.CX 4417 4556,
.measureX 4417 [] [.CZ 4159 4555,.CZ 4159 4416,.CZ 4555 4416],
.CX 4159 4555,
.CX 4416 4555,
.measureX 4416 [] [.CZ 4158 4554,.CZ 4158 4415,.CZ 4554 4415],
.CX 4158 4554,
.CX 4415 4554,
.measureX 4415 [] [.CZ 4157 4553,.CZ 4157 4414,.CZ 4553 4414],
.CX 4157 4553,
.CX 4414 4553,
.measureX 4414 [] [.CZ 4156 4552,.CZ 4156 4413,.CZ 4552 4413],
.CX 4156 4552,
.CX 4413 4552,
.measureX 4413 [] [.CZ 4155 4551,.CZ 4155 4412,.CZ 4551 4412],
.CX 4155 4551,
.CX 4412 4551,
.measureX 4412 [] [.CZ 4154 4550,.CZ 4154 4411,.CZ 4550 4411],
.CX 4154 4550,
.CX 4411 4550,
.measureX 4411 [] [.CZ 4153 4549,.CZ 4153 4410,.CZ 4549 4410],
.CX 4153 4549,
.CX 4410 4549,
.measureX 4410 [] [.CZ 4152 4548,.CZ 4152 4409,.CZ 4548 4409],
.CX 4152 4548,
.CX 4409 4548,
.measureX 4409 [] [.CZ 4151 4547,.CZ 4151 4408,.CZ 4547 4408],
.CX 4151 4547,
.CX 4408 4547,
.measureX 4408 [] [.CZ 4150 4546,.CZ 4150 4407,.CZ 4546 4407],
.CX 4150 4546,
.CX 4407 4546,
.measureX 4407 [] [.CZ 4149 4545,.CZ 4149 4406,.CZ 4545 4406],
.CX 4149 4545,
.CX 4406 4545,
.measureX 4406 [] [.CZ 4148 4544,.CZ 4148 4405,.CZ 4544 4405],
.CX 4148 4544,
.CX 4405 4544,
.measureX 4405 [] [.CZ 4147 4543,.CZ 4147 4404,.CZ 4543 4404],
.CX 4147 4543,
.CX 4404 4543,
.measureX 4404 [] [.CZ 4146 4542,.CZ 4146 4403,.CZ 4542 4403],
.CX 4146 4542,
.CX 4403 4542,
.measureX 4403 [] [.CZ 4145 4541,.CZ 4145 4402,.CZ 4541 4402],
.CX 4145 4541,
.CX 4402 4541,
.measureX 4402 [] [.CZ 4144 4540,.CZ 4144 4401,.CZ 4540 4401],
.CX 4144 4540,
.CX 4401 4540,
.measureX 4401 [] [.CZ 4143 4539,.CZ 4143 4400,.CZ 4539 4400],
.CX 4143 4539,
.CX 4400 4539,
.measureX 4400 [] [.CZ 4142 4538,.CZ 4142 4399,.CZ 4538 4399],
.CX 4142 4538,
.CX 4399 4538,
.measureX 4399 [] [.CZ 4141 4537,.CZ 4141 4398,.CZ 4537 4398],
.CX 4141 4537,
.CX 4398 4537,
.measureX 4398 [] [.CZ 4140 4536,.CZ 4140 4397,.CZ 4536 4397],
.CX 4140 4536,
.CX 4397 4536,
.measureX 4397 [] [.CZ 4139 4535,.CZ 4139 4396,.CZ 4535 4396],
.CX 4139 4535,
.CX 4396 4535,
.measureX 4396 [] [.CZ 4138 4534,.CZ 4138 4395,.CZ 4534 4395],
.CX 4138 4534,
.CX 4395 4534,
.measureX 4395 [] [.CZ 4137 4533,.CZ 4137 4394,.CZ 4533 4394],
.CX 4137 4533,
.CX 4394 4533,
.measureX 4394 [] [.CZ 4136 4532,.CZ 4136 4393,.CZ 4532 4393],
.CX 4136 4532,
.CX 4393 4532,
.measureX 4393 [] [.CZ 4135 4531,.CZ 4135 4392,.CZ 4531 4392],
.CX 4135 4531,
.CX 4392 4531,
.measureX 4392 [] [.CZ 4134 4530,.CZ 4134 4391,.CZ 4530 4391],
.CX 4134 4530,
.CX 4391 4530,
.measureX 4391 [] [.CZ 4133 4529,.CZ 4133 4390,.CZ 4529 4390],
.CX 4133 4529,
.CX 4390 4529,
.measureX 4390 [] [.CZ 4132 4528,.CZ 4132 4389,.CZ 4528 4389],
.CX 4132 4528
]
def chunk11 : Program := [
.CX 4389 4528,
.measureX 4389 [] [.CZ 4131 4527,.CZ 4131 4388,.CZ 4527 4388],
.CX 4131 4527,
.CX 4388 4527,
.measureX 4388 [] [.CZ 4130 4526,.CZ 4130 4387,.CZ 4526 4387],
.CX 4130 4526,
.CX 4387 4526,
.measureX 4387 [] [.CZ 4129 4525,.CZ 4129 4386,.CZ 4525 4386],
.CX 4129 4525,
.CX 4386 4525,
.measureX 4386 [] [.CZ 4128 4524,.CZ 4128 4385,.CZ 4524 4385],
.CX 4128 4524,
.CX 4385 4524,
.measureX 4385 [] [.CZ 4127 4523,.CZ 4127 4384,.CZ 4523 4384],
.CX 4127 4523,
.CX 4384 4523,
.measureX 4384 [] [.CZ 4126 4522,.CZ 4126 4383,.CZ 4522 4383],
.CX 4126 4522,
.CX 4383 4522,
.measureX 4383 [] [.CZ 4125 4521,.CZ 4125 4382,.CZ 4521 4382],
.CX 4125 4521,
.CX 4382 4521,
.measureX 4382 [] [.CZ 4124 4520,.CZ 4124 4381,.CZ 4520 4381],
.CX 4124 4520,
.CX 4381 4520,
.measureX 4381 [] [.CZ 4123 4519,.CZ 4123 4380,.CZ 4519 4380],
.CX 4123 4519,
.CX 4380 4519,
.measureX 4380 [] [.CZ 4122 4518,.CZ 4122 4379,.CZ 4518 4379],
.CX 4122 4518,
.CX 4379 4518,
.measureX 4379 [] [.CZ 4121 4517,.CZ 4121 4378,.CZ 4517 4378],
.CX 4121 4517,
.CX 4378 4517,
.measureX 4378 [] [.CZ 4120 4516,.CZ 4120 4377,.CZ 4516 4377],
.CX 4120 4516,
.CX 4377 4516,
.measureX 4377 [] [.CZ 4119 4515,.CZ 4119 4376,.CZ 4515 4376],
.CX 4119 4515,
.CX 4376 4515,
.measureX 4376 [] [.CZ 4118 4514,.CZ 4118 4375,.CZ 4514 4375],
.CX 4118 4514,
.CX 4375 4514,
.measureX 4375 [] [.CZ 4117 4513,.CZ 4117 4374,.CZ 4513 4374],
.CX 4117 4513,
.CX 4374 4513,
.measureX 4374 [] [.CZ 4116 4512,.CZ 4116 4373,.CZ 4512 4373],
.CX 4116 4512,
.CX 4373 4512,
.measureX 4373 [] [.CZ 4115 4511,.CZ 4115 4760,.CZ 4511 4760],
.CX 4115 4511,
.CX 4760 4511,
.X 4507,
.X 4508,
.X 4509,
.X 4510,
.X 4511,
.X 4512,
.X 4513,
.X 4514,
.X 4515,
.X 4516,
.X 4517,
.X 4518,
.X 4519,
.X 4520,
.X 4521,
.X 4522,
.X 4523,
.X 4524,
.X 4525,
.X 4526,
.X 4527,
.X 4528,
.X 4529,
.X 4530,
.X 4531,
.X 4532,
.X 4533,
.X 4534,
.X 4535,
.X 4536,
.X 4537,
.X 4538,
.X 4539,
.X 4540,
.X 4541,
.X 4542,
.X 4543,
.X 4544,
.X 4545,
.X 4546,
.X 4547,
.X 4548,
.X 4549,
.X 4550,
.X 4551,
.X 4552,
.X 4553,
.X 4554,
.X 4555,
.X 4556,
.X 4557,
.X 4558,
.X 4559,
.X 4560,
.X 4561,
.X 4562,
.X 4563,
.X 4564,
.X 4565,
.X 4566,
.X 4567,
.X 4568,
.X 4569,
.X 4570,
.X 4571,
.X 4572,
.X 4573,
.X 4574,
.X 4575,
.X 4576,
.X 4577,
.X 4578,
.X 4579,
.X 4580,
.X 4581,
.X 4582
]
def chunk12 : Program := [
.X 4583,
.X 4584,
.X 4585,
.X 4586,
.X 4587,
.X 4588,
.X 4589,
.X 4590,
.X 4591,
.X 4592,
.X 4593,
.X 4594,
.X 4595,
.X 4596,
.X 4597,
.X 4598,
.X 4599,
.X 4600,
.X 4601,
.X 4602,
.X 4603,
.X 4604,
.X 4605,
.X 4606,
.X 4607,
.X 4608,
.X 4609,
.X 4610,
.X 4611,
.X 4612,
.X 4613,
.X 4614,
.X 4615,
.X 4616,
.X 4617,
.X 4618,
.X 4619,
.X 4620,
.X 4621,
.X 4622,
.X 4623,
.X 4624,
.X 4625,
.X 4626,
.X 4627,
.X 4628,
.X 4629,
.X 4630,
.X 4631,
.X 4632,
.X 4633,
.X 4634,
.X 4635,
.X 4636,
.X 4637,
.X 4638,
.X 4639,
.X 4640,
.X 4641,
.CX 4115 4507,
.CX 4115 4760,
.CCX 4507 4760 4373,
.CX 4115 4373,
.CX 4115 4760,
.CX 4115 4507,
.CX 4116 4508,
.CX 4116 4373,
.CCX 4508 4373 4374,
.CX 4116 4374,
.CX 4116 4373,
.CX 4116 4508,
.CX 4117 4509,
.CX 4117 4374,
.CCX 4509 4374 4375,
.CX 4117 4375,
.CX 4117 4374,
.CX 4117 4509,
.CX 4118 4510,
.CX 4118 4375,
.CCX 4510 4375 4376,
.CX 4118 4376,
.CX 4118 4375,
.CX 4118 4510,
.CX 4119 4511,
.CX 4119 4376,
.CCX 4511 4376 4377,
.CX 4119 4377,
.CX 4119 4376,
.CX 4119 4511,
.CX 4120 4512,
.CX 4120 4377,
.CCX 4512 4377 4378,
.CX 4120 4378,
.CX 4120 4377,
.CX 4120 4512,
.CX 4121 4513,
.CX 4121 4378,
.CCX 4513 4378 4379,
.CX 4121 4379,
.CX 4121 4378,
.CX 4121 4513,
.CX 4122 4514,
.CX 4122 4379,
.CCX 4514 4379 4380,
.CX 4122 4380,
.CX 4122 4379,
.CX 4122 4514,
.CX 4123 4515,
.CX 4123 4380,
.CCX 4515 4380 4381,
.CX 4123 4381,
.CX 4123 4380,
.CX 4123 4515,
.CX 4124 4516,
.CX 4124 4381,
.CCX 4516 4381 4382,
.CX 4124 4382,
.CX 4124 4381,
.CX 4124 4516,
.CX 4125 4517,
.CX 4125 4382,
.CCX 4517 4382 4383,
.CX 4125 4383,
.CX 4125 4382,
.CX 4125 4517,
.CX 4126 4518,
.CX 4126 4383,
.CCX 4518 4383 4384
]
def chunk13 : Program := [
.CX 4126 4384,
.CX 4126 4383,
.CX 4126 4518,
.CX 4127 4519,
.CX 4127 4384,
.CCX 4519 4384 4385,
.CX 4127 4385,
.CX 4127 4384,
.CX 4127 4519,
.CX 4128 4520,
.CX 4128 4385,
.CCX 4520 4385 4386,
.CX 4128 4386,
.CX 4128 4385,
.CX 4128 4520,
.CX 4129 4521,
.CX 4129 4386,
.CCX 4521 4386 4387,
.CX 4129 4387,
.CX 4129 4386,
.CX 4129 4521,
.CX 4130 4522,
.CX 4130 4387,
.CCX 4522 4387 4388,
.CX 4130 4388,
.CX 4130 4387,
.CX 4130 4522,
.CX 4131 4523,
.CX 4131 4388,
.CCX 4523 4388 4389,
.CX 4131 4389,
.CX 4131 4388,
.CX 4131 4523,
.CX 4132 4524,
.CX 4132 4389,
.CCX 4524 4389 4390,
.CX 4132 4390,
.CX 4132 4389,
.CX 4132 4524,
.CX 4133 4525,
.CX 4133 4390,
.CCX 4525 4390 4391,
.CX 4133 4391,
.CX 4133 4390,
.CX 4133 4525,
.CX 4134 4526,
.CX 4134 4391,
.CCX 4526 4391 4392,
.CX 4134 4392,
.CX 4134 4391,
.CX 4134 4526,
.CX 4135 4527,
.CX 4135 4392,
.CCX 4527 4392 4393,
.CX 4135 4393,
.CX 4135 4392,
.CX 4135 4527,
.CX 4136 4528,
.CX 4136 4393,
.CCX 4528 4393 4394,
.CX 4136 4394,
.CX 4136 4393,
.CX 4136 4528,
.CX 4137 4529,
.CX 4137 4394,
.CCX 4529 4394 4395,
.CX 4137 4395,
.CX 4137 4394,
.CX 4137 4529,
.CX 4138 4530,
.CX 4138 4395,
.CCX 4530 4395 4396,
.CX 4138 4396,
.CX 4138 4395,
.CX 4138 4530,
.CX 4139 4531,
.CX 4139 4396,
.CCX 4531 4396 4397,
.CX 4139 4397,
.CX 4139 4396,
.CX 4139 4531,
.CX 4140 4532,
.CX 4140 4397,
.CCX 4532 4397 4398,
.CX 4140 4398,
.CX 4140 4397,
.CX 4140 4532,
.CX 4141 4533,
.CX 4141 4398,
.CCX 4533 4398 4399,
.CX 4141 4399,
.CX 4141 4398,
.CX 4141 4533,
.CX 4142 4534,
.CX 4142 4399,
.CCX 4534 4399 4400,
.CX 4142 4400,
.CX 4142 4399,
.CX 4142 4534,
.CX 4143 4535,
.CX 4143 4400,
.CCX 4535 4400 4401,
.CX 4143 4401,
.CX 4143 4400,
.CX 4143 4535,
.CX 4144 4536,
.CX 4144 4401,
.CCX 4536 4401 4402,
.CX 4144 4402,
.CX 4144 4401,
.CX 4144 4536,
.CX 4145 4537,
.CX 4145 4402,
.CCX 4537 4402 4403,
.CX 4145 4403,
.CX 4145 4402,
.CX 4145 4537,
.CX 4146 4538,
.CX 4146 4403,
.CCX 4538 4403 4404,
.CX 4146 4404,
.CX 4146 4403,
.CX 4146 4538,
.CX 4147 4539,
.CX 4147 4404,
.CCX 4539 4404 4405,
.CX 4147 4405,
.CX 4147 4404
]
def chunk14 : Program := [
.CX 4147 4539,
.CX 4148 4540,
.CX 4148 4405,
.CCX 4540 4405 4406,
.CX 4148 4406,
.CX 4148 4405,
.CX 4148 4540,
.CX 4149 4541,
.CX 4149 4406,
.CCX 4541 4406 4407,
.CX 4149 4407,
.CX 4149 4406,
.CX 4149 4541,
.CX 4150 4542,
.CX 4150 4407,
.CCX 4542 4407 4408,
.CX 4150 4408,
.CX 4150 4407,
.CX 4150 4542,
.CX 4151 4543,
.CX 4151 4408,
.CCX 4543 4408 4409,
.CX 4151 4409,
.CX 4151 4408,
.CX 4151 4543,
.CX 4152 4544,
.CX 4152 4409,
.CCX 4544 4409 4410,
.CX 4152 4410,
.CX 4152 4409,
.CX 4152 4544,
.CX 4153 4545,
.CX 4153 4410,
.CCX 4545 4410 4411,
.CX 4153 4411,
.CX 4153 4410,
.CX 4153 4545,
.CX 4154 4546,
.CX 4154 4411,
.CCX 4546 4411 4412,
.CX 4154 4412,
.CX 4154 4411,
.CX 4154 4546,
.CX 4155 4547,
.CX 4155 4412,
.CCX 4547 4412 4413,
.CX 4155 4413,
.CX 4155 4412,
.CX 4155 4547,
.CX 4156 4548,
.CX 4156 4413,
.CCX 4548 4413 4414,
.CX 4156 4414,
.CX 4156 4413,
.CX 4156 4548,
.CX 4157 4549,
.CX 4157 4414,
.CCX 4549 4414 4415,
.CX 4157 4415,
.CX 4157 4414,
.CX 4157 4549,
.CX 4158 4550,
.CX 4158 4415,
.CCX 4550 4415 4416,
.CX 4158 4416,
.CX 4158 4415,
.CX 4158 4550,
.CX 4159 4551,
.CX 4159 4416,
.CCX 4551 4416 4417,
.CX 4159 4417,
.CX 4159 4416,
.CX 4159 4551,
.CX 4160 4552,
.CX 4160 4417,
.CCX 4552 4417 4418,
.CX 4160 4418,
.CX 4160 4417,
.CX 4160 4552,
.CX 4161 4553,
.CX 4161 4418,
.CCX 4553 4418 4419,
.CX 4161 4419,
.CX 4161 4418,
.CX 4161 4553,
.CX 4162 4554,
.CX 4162 4419,
.CCX 4554 4419 4420,
.CX 4162 4420,
.CX 4162 4419,
.CX 4162 4554,
.CX 4163 4555,
.CX 4163 4420,
.CCX 4555 4420 4421,
.CX 4163 4421,
.CX 4163 4420,
.CX 4163 4555,
.CX 4164 4556,
.CX 4164 4421,
.CCX 4556 4421 4422,
.CX 4164 4422,
.CX 4164 4421,
.CX 4164 4556,
.CX 4165 4557,
.CX 4165 4422,
.CCX 4557 4422 4423,
.CX 4165 4423,
.CX 4165 4422,
.CX 4165 4557,
.CX 4166 4558,
.CX 4166 4423,
.CCX 4558 4423 4424,
.CX 4166 4424,
.CX 4166 4423,
.CX 4166 4558,
.CX 4167 4559,
.CX 4167 4424,
.CCX 4559 4424 4425,
.CX 4167 4425,
.CX 4167 4424,
.CX 4167 4559,
.CX 4168 4560,
.CX 4168 4425,
.CCX 4560 4425 4426,
.CX 4168 4426,
.CX 4168 4425,
.CX 4168 4560,
.CX 4169 4561
]
def chunk15 : Program := [
.CX 4169 4426,
.CCX 4561 4426 4427,
.CX 4169 4427,
.CX 4169 4426,
.CX 4169 4561,
.CX 4170 4562,
.CX 4170 4427,
.CCX 4562 4427 4428,
.CX 4170 4428,
.CX 4170 4427,
.CX 4170 4562,
.CX 4171 4563,
.CX 4171 4428,
.CCX 4563 4428 4429,
.CX 4171 4429,
.CX 4171 4428,
.CX 4171 4563,
.CX 4172 4564,
.CX 4172 4429,
.CCX 4564 4429 4430,
.CX 4172 4430,
.CX 4172 4429,
.CX 4172 4564,
.CX 4173 4565,
.CX 4173 4430,
.CCX 4565 4430 4431,
.CX 4173 4431,
.CX 4173 4430,
.CX 4173 4565,
.CX 4174 4566,
.CX 4174 4431,
.CCX 4566 4431 4432,
.CX 4174 4432,
.CX 4174 4431,
.CX 4174 4566,
.CX 4175 4567,
.CX 4175 4432,
.CCX 4567 4432 4433,
.CX 4175 4433,
.CX 4175 4432,
.CX 4175 4567,
.CX 4176 4568,
.CX 4176 4433,
.CCX 4568 4433 4434,
.CX 4176 4434,
.CX 4176 4433,
.CX 4176 4568,
.CX 4177 4569,
.CX 4177 4434,
.CCX 4569 4434 4435,
.CX 4177 4435,
.CX 4177 4434,
.CX 4177 4569,
.CX 4178 4570,
.CX 4178 4435,
.CCX 4570 4435 4436,
.CX 4178 4436,
.CX 4178 4435,
.CX 4178 4570,
.CX 4179 4571,
.CX 4179 4436,
.CCX 4571 4436 4437,
.CX 4179 4437,
.CX 4179 4436,
.CX 4179 4571,
.CX 4180 4572,
.CX 4180 4437,
.CCX 4572 4437 4438,
.CX 4180 4438,
.CX 4180 4437,
.CX 4180 4572,
.CX 4181 4573,
.CX 4181 4438,
.CCX 4573 4438 4439,
.CX 4181 4439,
.CX 4181 4438,
.CX 4181 4573,
.CX 4182 4574,
.CX 4182 4439,
.CCX 4574 4439 4440,
.CX 4182 4440,
.CX 4182 4439,
.CX 4182 4574,
.CX 4183 4575,
.CX 4183 4440,
.CCX 4575 4440 4441,
.CX 4183 4441,
.CX 4183 4440,
.CX 4183 4575,
.CX 4184 4576,
.CX 4184 4441,
.CCX 4576 4441 4442,
.CX 4184 4442,
.CX 4184 4441,
.CX 4184 4576,
.CX 4185 4577,
.CX 4185 4442,
.CCX 4577 4442 4443,
.CX 4185 4443,
.CX 4185 4442,
.CX 4185 4577,
.CX 4186 4578,
.CX 4186 4443,
.CCX 4578 4443 4444,
.CX 4186 4444,
.CX 4186 4443,
.CX 4186 4578,
.CX 4187 4579,
.CX 4187 4444,
.CCX 4579 4444 4445,
.CX 4187 4445,
.CX 4187 4444,
.CX 4187 4579,
.CX 4188 4580,
.CX 4188 4445,
.CCX 4580 4445 4446,
.CX 4188 4446,
.CX 4188 4445,
.CX 4188 4580,
.CX 4189 4581,
.CX 4189 4446,
.CCX 4581 4446 4447,
.CX 4189 4447,
.CX 4189 4446,
.CX 4189 4581,
.CX 4190 4582,
.CX 4190 4447,
.CCX 4582 4447 4448
]
def chunk16 : Program := [
.CX 4190 4448,
.CX 4190 4447,
.CX 4190 4582,
.CX 4191 4583,
.CX 4191 4448,
.CCX 4583 4448 4449,
.CX 4191 4449,
.CX 4191 4448,
.CX 4191 4583,
.CX 4192 4584,
.CX 4192 4449,
.CCX 4584 4449 4450,
.CX 4192 4450,
.CX 4192 4449,
.CX 4192 4584,
.CX 4193 4585,
.CX 4193 4450,
.CCX 4585 4450 4451,
.CX 4193 4451,
.CX 4193 4450,
.CX 4193 4585,
.CX 4194 4586,
.CX 4194 4451,
.CCX 4586 4451 4452,
.CX 4194 4452,
.CX 4194 4451,
.CX 4194 4586,
.CX 4195 4587,
.CX 4195 4452,
.CCX 4587 4452 4453,
.CX 4195 4453,
.CX 4195 4452,
.CX 4195 4587,
.CX 4196 4588,
.CX 4196 4453,
.CCX 4588 4453 4454,
.CX 4196 4454,
.CX 4196 4453,
.CX 4196 4588,
.CX 4197 4589,
.CX 4197 4454,
.CCX 4589 4454 4455,
.CX 4197 4455,
.CX 4197 4454,
.CX 4197 4589,
.CX 4198 4590,
.CX 4198 4455,
.CCX 4590 4455 4456,
.CX 4198 4456,
.CX 4198 4455,
.CX 4198 4590,
.CX 4199 4591,
.CX 4199 4456,
.CCX 4591 4456 4457,
.CX 4199 4457,
.CX 4199 4456,
.CX 4199 4591,
.CX 4200 4592,
.CX 4200 4457,
.CCX 4592 4457 4458,
.CX 4200 4458,
.CX 4200 4457,
.CX 4200 4592,
.CX 4201 4593,
.CX 4201 4458,
.CCX 4593 4458 4459,
.CX 4201 4459,
.CX 4201 4458,
.CX 4201 4593,
.CX 4202 4594,
.CX 4202 4459,
.CCX 4594 4459 4460,
.CX 4202 4460,
.CX 4202 4459,
.CX 4202 4594,
.CX 4203 4595,
.CX 4203 4460,
.CCX 4595 4460 4461,
.CX 4203 4461,
.CX 4203 4460,
.CX 4203 4595,
.CX 4204 4596,
.CX 4204 4461,
.CCX 4596 4461 4462,
.CX 4204 4462,
.CX 4204 4461,
.CX 4204 4596,
.CX 4205 4597,
.CX 4205 4462,
.CCX 4597 4462 4463,
.CX 4205 4463,
.CX 4205 4462,
.CX 4205 4597,
.CX 4206 4598,
.CX 4206 4463,
.CCX 4598 4463 4464,
.CX 4206 4464,
.CX 4206 4463,
.CX 4206 4598,
.CX 4207 4599,
.CX 4207 4464,
.CCX 4599 4464 4465,
.CX 4207 4465,
.CX 4207 4464,
.CX 4207 4599,
.CX 4208 4600,
.CX 4208 4465,
.CCX 4600 4465 4466,
.CX 4208 4466,
.CX 4208 4465,
.CX 4208 4600,
.CX 4209 4601,
.CX 4209 4466,
.CCX 4601 4466 4467,
.CX 4209 4467,
.CX 4209 4466,
.CX 4209 4601,
.CX 4210 4602,
.CX 4210 4467,
.CCX 4602 4467 4468,
.CX 4210 4468,
.CX 4210 4467,
.CX 4210 4602,
.CX 4211 4603,
.CX 4211 4468,
.CCX 4603 4468 4469,
.CX 4211 4469,
.CX 4211 4468
]
def chunk17 : Program := [
.CX 4211 4603,
.CX 4212 4604,
.CX 4212 4469,
.CCX 4604 4469 4470,
.CX 4212 4470,
.CX 4212 4469,
.CX 4212 4604,
.CX 4213 4605,
.CX 4213 4470,
.CCX 4605 4470 4471,
.CX 4213 4471,
.CX 4213 4470,
.CX 4213 4605,
.CX 4214 4606,
.CX 4214 4471,
.CCX 4606 4471 4472,
.CX 4214 4472,
.CX 4214 4471,
.CX 4214 4606,
.CX 4215 4607,
.CX 4215 4472,
.CCX 4607 4472 4473,
.CX 4215 4473,
.CX 4215 4472,
.CX 4215 4607,
.CX 4216 4608,
.CX 4216 4473,
.CCX 4608 4473 4474,
.CX 4216 4474,
.CX 4216 4473,
.CX 4216 4608,
.CX 4217 4609,
.CX 4217 4474,
.CCX 4609 4474 4475,
.CX 4217 4475,
.CX 4217 4474,
.CX 4217 4609,
.CX 4218 4610,
.CX 4218 4475,
.CCX 4610 4475 4476,
.CX 4218 4476,
.CX 4218 4475,
.CX 4218 4610,
.CX 4219 4611,
.CX 4219 4476,
.CCX 4611 4476 4477,
.CX 4219 4477,
.CX 4219 4476,
.CX 4219 4611,
.CX 4220 4612,
.CX 4220 4477,
.CCX 4612 4477 4478,
.CX 4220 4478,
.CX 4220 4477,
.CX 4220 4612,
.CX 4221 4613,
.CX 4221 4478,
.CCX 4613 4478 4479,
.CX 4221 4479,
.CX 4221 4478,
.CX 4221 4613,
.CX 4222 4614,
.CX 4222 4479,
.CCX 4614 4479 4480,
.CX 4222 4480,
.CX 4222 4479,
.CX 4222 4614,
.CX 4223 4615,
.CX 4223 4480,
.CCX 4615 4480 4481,
.CX 4223 4481,
.CX 4223 4480,
.CX 4223 4615,
.CX 4224 4616,
.CX 4224 4481,
.CCX 4616 4481 4482,
.CX 4224 4482,
.CX 4224 4481,
.CX 4224 4616,
.CX 4225 4617,
.CX 4225 4482,
.CCX 4617 4482 4483,
.CX 4225 4483,
.CX 4225 4482,
.CX 4225 4617,
.CX 4226 4618,
.CX 4226 4483,
.CCX 4618 4483 4484,
.CX 4226 4484,
.CX 4226 4483,
.CX 4226 4618,
.CX 4227 4619,
.CX 4227 4484,
.CCX 4619 4484 4485,
.CX 4227 4485,
.CX 4227 4484,
.CX 4227 4619,
.CX 4228 4620,
.CX 4228 4485,
.CCX 4620 4485 4486,
.CX 4228 4486,
.CX 4228 4485,
.CX 4228 4620,
.CX 4229 4621,
.CX 4229 4486,
.CCX 4621 4486 4487,
.CX 4229 4487,
.CX 4229 4486,
.CX 4229 4621,
.CX 4230 4622,
.CX 4230 4487,
.CCX 4622 4487 4488,
.CX 4230 4488,
.CX 4230 4487,
.CX 4230 4622,
.CX 4231 4623,
.CX 4231 4488,
.CCX 4623 4488 4489,
.CX 4231 4489,
.CX 4231 4488,
.CX 4231 4623,
.CX 4232 4624,
.CX 4232 4489,
.CCX 4624 4489 4490,
.CX 4232 4490,
.CX 4232 4489,
.CX 4232 4624,
.CX 4233 4625
]
def chunk18 : Program := [
.CX 4233 4490,
.CCX 4625 4490 4491,
.CX 4233 4491,
.CX 4233 4490,
.CX 4233 4625,
.CX 4234 4626,
.CX 4234 4491,
.CCX 4626 4491 4492,
.CX 4234 4492,
.CX 4234 4491,
.CX 4234 4626,
.CX 4235 4627,
.CX 4235 4492,
.CCX 4627 4492 4493,
.CX 4235 4493,
.CX 4235 4492,
.CX 4235 4627,
.CX 4236 4628,
.CX 4236 4493,
.CCX 4628 4493 4494,
.CX 4236 4494,
.CX 4236 4493,
.CX 4236 4628,
.CX 4237 4629,
.CX 4237 4494,
.CCX 4629 4494 4495,
.CX 4237 4495,
.CX 4237 4494,
.CX 4237 4629,
.CX 4238 4630,
.CX 4238 4495,
.CCX 4630 4495 4496,
.CX 4238 4496,
.CX 4238 4495,
.CX 4238 4630,
.CX 4239 4631,
.CX 4239 4496,
.CCX 4631 4496 4497,
.CX 4239 4497,
.CX 4239 4496,
.CX 4239 4631,
.CX 4240 4632,
.CX 4240 4497,
.CCX 4632 4497 4498,
.CX 4240 4498,
.CX 4240 4497,
.CX 4240 4632,
.CX 4241 4633,
.CX 4241 4498,
.CCX 4633 4498 4499,
.CX 4241 4499,
.CX 4241 4498,
.CX 4241 4633,
.CX 4242 4634,
.CX 4242 4499,
.CCX 4634 4499 4500,
.CX 4242 4500,
.CX 4242 4499,
.CX 4242 4634,
.CX 4371 4635,
.CX 4371 4500,
.CCX 4635 4500 4764,
.CX 4371 4764,
.CX 4371 4500,
.CX 4371 4635,
.CX 4372 4636,
.CX 4372 4764,
.CCX 4636 4764 4765,
.CX 4372 4765,
.CX 4372 4764,
.CX 4372 4636,
.CX 4697 4637,
.CX 4697 4765,
.CCX 4637 4765 4766,
.CX 4697 4766,
.CX 4697 4765,
.CX 4697 4637,
.CX 4698 4638,
.CX 4698 4766,
.CCX 4638 4766 4767,
.CX 4698 4767,
.CX 4698 4766,
.CX 4698 4638,
.CX 4699 4639,
.CX 4699 4767,
.CCX 4639 4767 4768,
.CX 4699 4768,
.CX 4699 4767,
.CX 4699 4639,
.CX 4701 4769,
.CX 4641 4769,
.X 4769,
.CX 4701 4641,
.CX 4769 4641,
.measureX 4769 [] [.CZ 4700 4640,.CZ 4700 4768,.CZ 4640 4768],
.CX 4700 4640,
.CX 4768 4640,
.measureX 4768 [] [.CZ 4699 4639,.CZ 4699 4767,.CZ 4639 4767],
.CX 4699 4639,
.CX 4767 4639,
.measureX 4767 [] [.CZ 4698 4638,.CZ 4698 4766,.CZ 4638 4766],
.CX 4698 4638,
.CX 4766 4638,
.measureX 4766 [] [.CZ 4697 4637,.CZ 4697 4765,.CZ 4637 4765],
.CX 4697 4637,
.CX 4765 4637,
.measureX 4765 [] [.CZ 4372 4636,.CZ 4372 4764,.CZ 4636 4764],
.CX 4372 4636,
.CX 4764 4636,
.measureX 4764 [] [.CZ 4371 4635,.CZ 4371 4500,.CZ 4635 4500],
.CX 4371 4635,
.CX 4500 4635,
.measureX 4500 [] [.CZ 4242 4634,.CZ 4242 4499,.CZ 4634 4499],
.CX 4242 4634,
.CX 4499 4634,
.measureX 4499 [] [.CZ 4241 4633,.CZ 4241 4498,.CZ 4633 4498],
.CX 4241 4633,
.CX 4498 4633,
.measureX 4498 [] [.CZ 4240 4632,.CZ 4240 4497,.CZ 4632 4497],
.CX 4240 4632,
.CX 4497 4632,
.measureX 4497 [] [.CZ 4239 4631,.CZ 4239 4496,.CZ 4631 4496],
.CX 4239 4631,
.CX 4496 4631,
.measureX 4496 [] [.CZ 4238 4630,.CZ 4238 4495,.CZ 4630 4495],
.CX 4238 4630,
.CX 4495 4630,
.measureX 4495 [] [.CZ 4237 4629,.CZ 4237 4494,.CZ 4629 4494]
]
def chunk19 : Program := [
.CX 4237 4629,
.CX 4494 4629,
.measureX 4494 [] [.CZ 4236 4628,.CZ 4236 4493,.CZ 4628 4493],
.CX 4236 4628,
.CX 4493 4628,
.measureX 4493 [] [.CZ 4235 4627,.CZ 4235 4492,.CZ 4627 4492],
.CX 4235 4627,
.CX 4492 4627,
.measureX 4492 [] [.CZ 4234 4626,.CZ 4234 4491,.CZ 4626 4491],
.CX 4234 4626,
.CX 4491 4626,
.measureX 4491 [] [.CZ 4233 4625,.CZ 4233 4490,.CZ 4625 4490],
.CX 4233 4625,
.CX 4490 4625,
.measureX 4490 [] [.CZ 4232 4624,.CZ 4232 4489,.CZ 4624 4489],
.CX 4232 4624,
.CX 4489 4624,
.measureX 4489 [] [.CZ 4231 4623,.CZ 4231 4488,.CZ 4623 4488],
.CX 4231 4623,
.CX 4488 4623,
.measureX 4488 [] [.CZ 4230 4622,.CZ 4230 4487,.CZ 4622 4487],
.CX 4230 4622,
.CX 4487 4622,
.measureX 4487 [] [.CZ 4229 4621,.CZ 4229 4486,.CZ 4621 4486],
.CX 4229 4621,
.CX 4486 4621,
.measureX 4486 [] [.CZ 4228 4620,.CZ 4228 4485,.CZ 4620 4485],
.CX 4228 4620,
.CX 4485 4620,
.measureX 4485 [] [.CZ 4227 4619,.CZ 4227 4484,.CZ 4619 4484],
.CX 4227 4619,
.CX 4484 4619,
.measureX 4484 [] [.CZ 4226 4618,.CZ 4226 4483,.CZ 4618 4483],
.CX 4226 4618,
.CX 4483 4618,
.measureX 4483 [] [.CZ 4225 4617,.CZ 4225 4482,.CZ 4617 4482],
.CX 4225 4617,
.CX 4482 4617,
.measureX 4482 [] [.CZ 4224 4616,.CZ 4224 4481,.CZ 4616 4481],
.CX 4224 4616,
.CX 4481 4616,
.measureX 4481 [] [.CZ 4223 4615,.CZ 4223 4480,.CZ 4615 4480],
.CX 4223 4615,
.CX 4480 4615,
.measureX 4480 [] [.CZ 4222 4614,.CZ 4222 4479,.CZ 4614 4479],
.CX 4222 4614,
.CX 4479 4614,
.measureX 4479 [] [.CZ 4221 4613,.CZ 4221 4478,.CZ 4613 4478],
.CX 4221 4613,
.CX 4478 4613,
.measureX 4478 [] [.CZ 4220 4612,.CZ 4220 4477,.CZ 4612 4477],
.CX 4220 4612,
.CX 4477 4612,
.measureX 4477 [] [.CZ 4219 4611,.CZ 4219 4476,.CZ 4611 4476],
.CX 4219 4611,
.CX 4476 4611,
.measureX 4476 [] [.CZ 4218 4610,.CZ 4218 4475,.CZ 4610 4475],
.CX 4218 4610,
.CX 4475 4610,
.measureX 4475 [] [.CZ 4217 4609,.CZ 4217 4474,.CZ 4609 4474],
.CX 4217 4609,
.CX 4474 4609,
.measureX 4474 [] [.CZ 4216 4608,.CZ 4216 4473,.CZ 4608 4473],
.CX 4216 4608,
.CX 4473 4608,
.measureX 4473 [] [.CZ 4215 4607,.CZ 4215 4472,.CZ 4607 4472],
.CX 4215 4607,
.CX 4472 4607,
.measureX 4472 [] [.CZ 4214 4606,.CZ 4214 4471,.CZ 4606 4471],
.CX 4214 4606,
.CX 4471 4606,
.measureX 4471 [] [.CZ 4213 4605,.CZ 4213 4470,.CZ 4605 4470],
.CX 4213 4605,
.CX 4470 4605,
.measureX 4470 [] [.CZ 4212 4604,.CZ 4212 4469,.CZ 4604 4469],
.CX 4212 4604,
.CX 4469 4604,
.measureX 4469 [] [.CZ 4211 4603,.CZ 4211 4468,.CZ 4603 4468],
.CX 4211 4603,
.CX 4468 4603,
.measureX 4468 [] [.CZ 4210 4602,.CZ 4210 4467,.CZ 4602 4467],
.CX 4210 4602,
.CX 4467 4602,
.measureX 4467 [] [.CZ 4209 4601,.CZ 4209 4466,.CZ 4601 4466],
.CX 4209 4601,
.CX 4466 4601,
.measureX 4466 [] [.CZ 4208 4600,.CZ 4208 4465,.CZ 4600 4465],
.CX 4208 4600,
.CX 4465 4600,
.measureX 4465 [] [.CZ 4207 4599,.CZ 4207 4464,.CZ 4599 4464],
.CX 4207 4599,
.CX 4464 4599,
.measureX 4464 [] [.CZ 4206 4598,.CZ 4206 4463,.CZ 4598 4463],
.CX 4206 4598,
.CX 4463 4598,
.measureX 4463 [] [.CZ 4205 4597,.CZ 4205 4462,.CZ 4597 4462],
.CX 4205 4597,
.CX 4462 4597,
.measureX 4462 [] [.CZ 4204 4596,.CZ 4204 4461,.CZ 4596 4461],
.CX 4204 4596,
.CX 4461 4596,
.measureX 4461 [] [.CZ 4203 4595,.CZ 4203 4460,.CZ 4595 4460],
.CX 4203 4595,
.CX 4460 4595,
.measureX 4460 [] [.CZ 4202 4594,.CZ 4202 4459,.CZ 4594 4459],
.CX 4202 4594,
.CX 4459 4594,
.measureX 4459 [] [.CZ 4201 4593,.CZ 4201 4458,.CZ 4593 4458],
.CX 4201 4593,
.CX 4458 4593,
.measureX 4458 [] [.CZ 4200 4592,.CZ 4200 4457,.CZ 4592 4457],
.CX 4200 4592,
.CX 4457 4592,
.measureX 4457 [] [.CZ 4199 4591,.CZ 4199 4456,.CZ 4591 4456],
.CX 4199 4591,
.CX 4456 4591,
.measureX 4456 [] [.CZ 4198 4590,.CZ 4198 4455,.CZ 4590 4455],
.CX 4198 4590,
.CX 4455 4590,
.measureX 4455 [] [.CZ 4197 4589,.CZ 4197 4454,.CZ 4589 4454],
.CX 4197 4589,
.CX 4454 4589,
.measureX 4454 [] [.CZ 4196 4588,.CZ 4196 4453,.CZ 4588 4453],
.CX 4196 4588,
.CX 4453 4588,
.measureX 4453 [] [.CZ 4195 4587,.CZ 4195 4452,.CZ 4587 4452],
.CX 4195 4587,
.CX 4452 4587
]
def chunk20 : Program := [
.measureX 4452 [] [.CZ 4194 4586,.CZ 4194 4451,.CZ 4586 4451],
.CX 4194 4586,
.CX 4451 4586,
.measureX 4451 [] [.CZ 4193 4585,.CZ 4193 4450,.CZ 4585 4450],
.CX 4193 4585,
.CX 4450 4585,
.measureX 4450 [] [.CZ 4192 4584,.CZ 4192 4449,.CZ 4584 4449],
.CX 4192 4584,
.CX 4449 4584,
.measureX 4449 [] [.CZ 4191 4583,.CZ 4191 4448,.CZ 4583 4448],
.CX 4191 4583,
.CX 4448 4583,
.measureX 4448 [] [.CZ 4190 4582,.CZ 4190 4447,.CZ 4582 4447],
.CX 4190 4582,
.CX 4447 4582,
.measureX 4447 [] [.CZ 4189 4581,.CZ 4189 4446,.CZ 4581 4446],
.CX 4189 4581,
.CX 4446 4581,
.measureX 4446 [] [.CZ 4188 4580,.CZ 4188 4445,.CZ 4580 4445],
.CX 4188 4580,
.CX 4445 4580,
.measureX 4445 [] [.CZ 4187 4579,.CZ 4187 4444,.CZ 4579 4444],
.CX 4187 4579,
.CX 4444 4579,
.measureX 4444 [] [.CZ 4186 4578,.CZ 4186 4443,.CZ 4578 4443],
.CX 4186 4578,
.CX 4443 4578,
.measureX 4443 [] [.CZ 4185 4577,.CZ 4185 4442,.CZ 4577 4442],
.CX 4185 4577,
.CX 4442 4577,
.measureX 4442 [] [.CZ 4184 4576,.CZ 4184 4441,.CZ 4576 4441],
.CX 4184 4576,
.CX 4441 4576,
.measureX 4441 [] [.CZ 4183 4575,.CZ 4183 4440,.CZ 4575 4440],
.CX 4183 4575,
.CX 4440 4575,
.measureX 4440 [] [.CZ 4182 4574,.CZ 4182 4439,.CZ 4574 4439],
.CX 4182 4574,
.CX 4439 4574,
.measureX 4439 [] [.CZ 4181 4573,.CZ 4181 4438,.CZ 4573 4438],
.CX 4181 4573,
.CX 4438 4573,
.measureX 4438 [] [.CZ 4180 4572,.CZ 4180 4437,.CZ 4572 4437],
.CX 4180 4572,
.CX 4437 4572,
.measureX 4437 [] [.CZ 4179 4571,.CZ 4179 4436,.CZ 4571 4436],
.CX 4179 4571,
.CX 4436 4571,
.measureX 4436 [] [.CZ 4178 4570,.CZ 4178 4435,.CZ 4570 4435],
.CX 4178 4570,
.CX 4435 4570,
.measureX 4435 [] [.CZ 4177 4569,.CZ 4177 4434,.CZ 4569 4434],
.CX 4177 4569,
.CX 4434 4569,
.measureX 4434 [] [.CZ 4176 4568,.CZ 4176 4433,.CZ 4568 4433],
.CX 4176 4568,
.CX 4433 4568,
.measureX 4433 [] [.CZ 4175 4567,.CZ 4175 4432,.CZ 4567 4432],
.CX 4175 4567,
.CX 4432 4567,
.measureX 4432 [] [.CZ 4174 4566,.CZ 4174 4431,.CZ 4566 4431],
.CX 4174 4566,
.CX 4431 4566,
.measureX 4431 [] [.CZ 4173 4565,.CZ 4173 4430,.CZ 4565 4430],
.CX 4173 4565,
.CX 4430 4565,
.measureX 4430 [] [.CZ 4172 4564,.CZ 4172 4429,.CZ 4564 4429],
.CX 4172 4564,
.CX 4429 4564,
.measureX 4429 [] [.CZ 4171 4563,.CZ 4171 4428,.CZ 4563 4428],
.CX 4171 4563,
.CX 4428 4563,
.measureX 4428 [] [.CZ 4170 4562,.CZ 4170 4427,.CZ 4562 4427],
.CX 4170 4562,
.CX 4427 4562,
.measureX 4427 [] [.CZ 4169 4561,.CZ 4169 4426,.CZ 4561 4426],
.CX 4169 4561,
.CX 4426 4561,
.measureX 4426 [] [.CZ 4168 4560,.CZ 4168 4425,.CZ 4560 4425],
.CX 4168 4560,
.CX 4425 4560,
.measureX 4425 [] [.CZ 4167 4559,.CZ 4167 4424,.CZ 4559 4424],
.CX 4167 4559,
.CX 4424 4559,
.measureX 4424 [] [.CZ 4166 4558,.CZ 4166 4423,.CZ 4558 4423],
.CX 4166 4558,
.CX 4423 4558,
.measureX 4423 [] [.CZ 4165 4557,.CZ 4165 4422,.CZ 4557 4422],
.CX 4165 4557,
.CX 4422 4557,
.measureX 4422 [] [.CZ 4164 4556,.CZ 4164 4421,.CZ 4556 4421],
.CX 4164 4556,
.CX 4421 4556,
.measureX 4421 [] [.CZ 4163 4555,.CZ 4163 4420,.CZ 4555 4420],
.CX 4163 4555,
.CX 4420 4555,
.measureX 4420 [] [.CZ 4162 4554,.CZ 4162 4419,.CZ 4554 4419],
.CX 4162 4554,
.CX 4419 4554,
.measureX 4419 [] [.CZ 4161 4553,.CZ 4161 4418,.CZ 4553 4418],
.CX 4161 4553,
.CX 4418 4553,
.measureX 4418 [] [.CZ 4160 4552,.CZ 4160 4417,.CZ 4552 4417],
.CX 4160 4552,
.CX 4417 4552,
.measureX 4417 [] [.CZ 4159 4551,.CZ 4159 4416,.CZ 4551 4416],
.CX 4159 4551,
.CX 4416 4551,
.measureX 4416 [] [.CZ 4158 4550,.CZ 4158 4415,.CZ 4550 4415],
.CX 4158 4550,
.CX 4415 4550,
.measureX 4415 [] [.CZ 4157 4549,.CZ 4157 4414,.CZ 4549 4414],
.CX 4157 4549,
.CX 4414 4549,
.measureX 4414 [] [.CZ 4156 4548,.CZ 4156 4413,.CZ 4548 4413],
.CX 4156 4548,
.CX 4413 4548,
.measureX 4413 [] [.CZ 4155 4547,.CZ 4155 4412,.CZ 4547 4412],
.CX 4155 4547,
.CX 4412 4547,
.measureX 4412 [] [.CZ 4154 4546,.CZ 4154 4411,.CZ 4546 4411],
.CX 4154 4546,
.CX 4411 4546,
.measureX 4411 [] [.CZ 4153 4545,.CZ 4153 4410,.CZ 4545 4410],
.CX 4153 4545,
.CX 4410 4545,
.measureX 4410 [] [.CZ 4152 4544,.CZ 4152 4409,.CZ 4544 4409],
.CX 4152 4544
]
def chunk21 : Program := [
.CX 4409 4544,
.measureX 4409 [] [.CZ 4151 4543,.CZ 4151 4408,.CZ 4543 4408],
.CX 4151 4543,
.CX 4408 4543,
.measureX 4408 [] [.CZ 4150 4542,.CZ 4150 4407,.CZ 4542 4407],
.CX 4150 4542,
.CX 4407 4542,
.measureX 4407 [] [.CZ 4149 4541,.CZ 4149 4406,.CZ 4541 4406],
.CX 4149 4541,
.CX 4406 4541,
.measureX 4406 [] [.CZ 4148 4540,.CZ 4148 4405,.CZ 4540 4405],
.CX 4148 4540,
.CX 4405 4540,
.measureX 4405 [] [.CZ 4147 4539,.CZ 4147 4404,.CZ 4539 4404],
.CX 4147 4539,
.CX 4404 4539,
.measureX 4404 [] [.CZ 4146 4538,.CZ 4146 4403,.CZ 4538 4403],
.CX 4146 4538,
.CX 4403 4538,
.measureX 4403 [] [.CZ 4145 4537,.CZ 4145 4402,.CZ 4537 4402],
.CX 4145 4537,
.CX 4402 4537,
.measureX 4402 [] [.CZ 4144 4536,.CZ 4144 4401,.CZ 4536 4401],
.CX 4144 4536,
.CX 4401 4536,
.measureX 4401 [] [.CZ 4143 4535,.CZ 4143 4400,.CZ 4535 4400],
.CX 4143 4535,
.CX 4400 4535,
.measureX 4400 [] [.CZ 4142 4534,.CZ 4142 4399,.CZ 4534 4399],
.CX 4142 4534,
.CX 4399 4534,
.measureX 4399 [] [.CZ 4141 4533,.CZ 4141 4398,.CZ 4533 4398],
.CX 4141 4533,
.CX 4398 4533,
.measureX 4398 [] [.CZ 4140 4532,.CZ 4140 4397,.CZ 4532 4397],
.CX 4140 4532,
.CX 4397 4532,
.measureX 4397 [] [.CZ 4139 4531,.CZ 4139 4396,.CZ 4531 4396],
.CX 4139 4531,
.CX 4396 4531,
.measureX 4396 [] [.CZ 4138 4530,.CZ 4138 4395,.CZ 4530 4395],
.CX 4138 4530,
.CX 4395 4530,
.measureX 4395 [] [.CZ 4137 4529,.CZ 4137 4394,.CZ 4529 4394],
.CX 4137 4529,
.CX 4394 4529,
.measureX 4394 [] [.CZ 4136 4528,.CZ 4136 4393,.CZ 4528 4393],
.CX 4136 4528,
.CX 4393 4528,
.measureX 4393 [] [.CZ 4135 4527,.CZ 4135 4392,.CZ 4527 4392],
.CX 4135 4527,
.CX 4392 4527,
.measureX 4392 [] [.CZ 4134 4526,.CZ 4134 4391,.CZ 4526 4391],
.CX 4134 4526,
.CX 4391 4526,
.measureX 4391 [] [.CZ 4133 4525,.CZ 4133 4390,.CZ 4525 4390],
.CX 4133 4525,
.CX 4390 4525,
.measureX 4390 [] [.CZ 4132 4524,.CZ 4132 4389,.CZ 4524 4389],
.CX 4132 4524,
.CX 4389 4524,
.measureX 4389 [] [.CZ 4131 4523,.CZ 4131 4388,.CZ 4523 4388],
.CX 4131 4523,
.CX 4388 4523,
.measureX 4388 [] [.CZ 4130 4522,.CZ 4130 4387,.CZ 4522 4387],
.CX 4130 4522,
.CX 4387 4522,
.measureX 4387 [] [.CZ 4129 4521,.CZ 4129 4386,.CZ 4521 4386],
.CX 4129 4521,
.CX 4386 4521,
.measureX 4386 [] [.CZ 4128 4520,.CZ 4128 4385,.CZ 4520 4385],
.CX 4128 4520,
.CX 4385 4520,
.measureX 4385 [] [.CZ 4127 4519,.CZ 4127 4384,.CZ 4519 4384],
.CX 4127 4519,
.CX 4384 4519,
.measureX 4384 [] [.CZ 4126 4518,.CZ 4126 4383,.CZ 4518 4383],
.CX 4126 4518,
.CX 4383 4518,
.measureX 4383 [] [.CZ 4125 4517,.CZ 4125 4382,.CZ 4517 4382],
.CX 4125 4517,
.CX 4382 4517,
.measureX 4382 [] [.CZ 4124 4516,.CZ 4124 4381,.CZ 4516 4381],
.CX 4124 4516,
.CX 4381 4516,
.measureX 4381 [] [.CZ 4123 4515,.CZ 4123 4380,.CZ 4515 4380],
.CX 4123 4515,
.CX 4380 4515,
.measureX 4380 [] [.CZ 4122 4514,.CZ 4122 4379,.CZ 4514 4379],
.CX 4122 4514,
.CX 4379 4514,
.measureX 4379 [] [.CZ 4121 4513,.CZ 4121 4378,.CZ 4513 4378],
.CX 4121 4513,
.CX 4378 4513,
.measureX 4378 [] [.CZ 4120 4512,.CZ 4120 4377,.CZ 4512 4377],
.CX 4120 4512,
.CX 4377 4512,
.measureX 4377 [] [.CZ 4119 4511,.CZ 4119 4376,.CZ 4511 4376],
.CX 4119 4511,
.CX 4376 4511,
.measureX 4376 [] [.CZ 4118 4510,.CZ 4118 4375,.CZ 4510 4375],
.CX 4118 4510,
.CX 4375 4510,
.measureX 4375 [] [.CZ 4117 4509,.CZ 4117 4374,.CZ 4509 4374],
.CX 4117 4509,
.CX 4374 4509,
.measureX 4374 [] [.CZ 4116 4508,.CZ 4116 4373,.CZ 4508 4373],
.CX 4116 4508,
.CX 4373 4508,
.measureX 4373 [] [.CZ 4115 4507,.CZ 4115 4760,.CZ 4507 4760],
.CX 4115 4507,
.CX 4760 4507,
.X 4507,
.X 4508,
.X 4509,
.X 4510,
.X 4511,
.X 4512,
.X 4513,
.X 4514,
.X 4515,
.X 4516,
.X 4517,
.X 4518,
.X 4519,
.X 4520,
.X 4521,
.X 4522
]
def chunk22 : Program := [
.X 4523,
.X 4524,
.X 4525,
.X 4526,
.X 4527,
.X 4528,
.X 4529,
.X 4530,
.X 4531,
.X 4532,
.X 4533,
.X 4534,
.X 4535,
.X 4536,
.X 4537,
.X 4538,
.X 4539,
.X 4540,
.X 4541,
.X 4542,
.X 4543,
.X 4544,
.X 4545,
.X 4546,
.X 4547,
.X 4548,
.X 4549,
.X 4550,
.X 4551,
.X 4552,
.X 4553,
.X 4554,
.X 4555,
.X 4556,
.X 4557,
.X 4558,
.X 4559,
.X 4560,
.X 4561,
.X 4562,
.X 4563,
.X 4564,
.X 4565,
.X 4566,
.X 4567,
.X 4568,
.X 4569,
.X 4570,
.X 4571,
.X 4572,
.X 4573,
.X 4574,
.X 4575,
.X 4576,
.X 4577,
.X 4578,
.X 4579,
.X 4580,
.X 4581,
.X 4582,
.X 4583,
.X 4584,
.X 4585,
.X 4586,
.X 4587,
.X 4588,
.X 4589,
.X 4590,
.X 4591,
.X 4592,
.X 4593,
.X 4594,
.X 4595,
.X 4596,
.X 4597,
.X 4598,
.X 4599,
.X 4600,
.X 4601,
.X 4602,
.X 4603,
.X 4604,
.X 4605,
.X 4606,
.X 4607,
.X 4608,
.X 4609,
.X 4610,
.X 4611,
.X 4612,
.X 4613,
.X 4614,
.X 4615,
.X 4616,
.X 4617,
.X 4618,
.X 4619,
.X 4620,
.X 4621,
.X 4622,
.X 4623,
.X 4624,
.X 4625,
.X 4626,
.X 4627,
.X 4628,
.X 4629,
.X 4630,
.X 4631,
.X 4632,
.X 4633,
.X 4634,
.X 4635,
.X 4636,
.X 4637,
.X 4638,
.X 4639,
.X 4640,
.X 4641,
.CX 4115 4533,
.CX 4115 4760,
.CCX 4533 4760 4373,
.CX 4115 4373,
.CX 4115 4760,
.CX 4115 4533,
.CX 4116 4534,
.CX 4116 4373,
.CCX 4534 4373 4374
]
def chunk23 : Program := [
.CX 4116 4374,
.CX 4116 4373,
.CX 4116 4534,
.CX 4117 4535,
.CX 4117 4374,
.CCX 4535 4374 4375,
.CX 4117 4375,
.CX 4117 4374,
.CX 4117 4535,
.CX 4118 4536,
.CX 4118 4375,
.CCX 4536 4375 4376,
.CX 4118 4376,
.CX 4118 4375,
.CX 4118 4536,
.CX 4119 4537,
.CX 4119 4376,
.CCX 4537 4376 4377,
.CX 4119 4377,
.CX 4119 4376,
.CX 4119 4537,
.CX 4120 4538,
.CX 4120 4377,
.CCX 4538 4377 4378,
.CX 4120 4378,
.CX 4120 4377,
.CX 4120 4538,
.CX 4121 4539,
.CX 4121 4378,
.CCX 4539 4378 4379,
.CX 4121 4379,
.CX 4121 4378,
.CX 4121 4539,
.CX 4122 4540,
.CX 4122 4379,
.CCX 4540 4379 4380,
.CX 4122 4380,
.CX 4122 4379,
.CX 4122 4540,
.CX 4123 4541,
.CX 4123 4380,
.CCX 4541 4380 4381,
.CX 4123 4381,
.CX 4123 4380,
.CX 4123 4541,
.CX 4124 4542,
.CX 4124 4381,
.CCX 4542 4381 4382,
.CX 4124 4382,
.CX 4124 4381,
.CX 4124 4542,
.CX 4125 4543,
.CX 4125 4382,
.CCX 4543 4382 4383,
.CX 4125 4383,
.CX 4125 4382,
.CX 4125 4543,
.CX 4126 4544,
.CX 4126 4383,
.CCX 4544 4383 4384,
.CX 4126 4384,
.CX 4126 4383,
.CX 4126 4544,
.CX 4127 4545,
.CX 4127 4384,
.CCX 4545 4384 4385,
.CX 4127 4385,
.CX 4127 4384,
.CX 4127 4545,
.CX 4128 4546,
.CX 4128 4385,
.CCX 4546 4385 4386,
.CX 4128 4386,
.CX 4128 4385,
.CX 4128 4546,
.CX 4129 4547,
.CX 4129 4386,
.CCX 4547 4386 4387,
.CX 4129 4387,
.CX 4129 4386,
.CX 4129 4547,
.CX 4130 4548,
.CX 4130 4387,
.CCX 4548 4387 4388,
.CX 4130 4388,
.CX 4130 4387,
.CX 4130 4548,
.CX 4131 4549,
.CX 4131 4388,
.CCX 4549 4388 4389,
.CX 4131 4389,
.CX 4131 4388,
.CX 4131 4549,
.CX 4132 4550,
.CX 4132 4389,
.CCX 4550 4389 4390,
.CX 4132 4390,
.CX 4132 4389,
.CX 4132 4550,
.CX 4133 4551,
.CX 4133 4390,
.CCX 4551 4390 4391,
.CX 4133 4391,
.CX 4133 4390,
.CX 4133 4551,
.CX 4134 4552,
.CX 4134 4391,
.CCX 4552 4391 4392,
.CX 4134 4392,
.CX 4134 4391,
.CX 4134 4552,
.CX 4135 4553,
.CX 4135 4392,
.CCX 4553 4392 4393,
.CX 4135 4393,
.CX 4135 4392,
.CX 4135 4553,
.CX 4136 4554,
.CX 4136 4393,
.CCX 4554 4393 4394,
.CX 4136 4394,
.CX 4136 4393,
.CX 4136 4554,
.CX 4137 4555,
.CX 4137 4394,
.CCX 4555 4394 4395,
.CX 4137 4395,
.CX 4137 4394
]
def chunk24 : Program := [
.CX 4137 4555,
.CX 4138 4556,
.CX 4138 4395,
.CCX 4556 4395 4396,
.CX 4138 4396,
.CX 4138 4395,
.CX 4138 4556,
.CX 4139 4557,
.CX 4139 4396,
.CCX 4557 4396 4397,
.CX 4139 4397,
.CX 4139 4396,
.CX 4139 4557,
.CX 4140 4558,
.CX 4140 4397,
.CCX 4558 4397 4398,
.CX 4140 4398,
.CX 4140 4397,
.CX 4140 4558,
.CX 4141 4559,
.CX 4141 4398,
.CCX 4559 4398 4399,
.CX 4141 4399,
.CX 4141 4398,
.CX 4141 4559,
.CX 4142 4560,
.CX 4142 4399,
.CCX 4560 4399 4400,
.CX 4142 4400,
.CX 4142 4399,
.CX 4142 4560,
.CX 4143 4561,
.CX 4143 4400,
.CCX 4561 4400 4401,
.CX 4143 4401,
.CX 4143 4400,
.CX 4143 4561,
.CX 4144 4562,
.CX 4144 4401,
.CCX 4562 4401 4402,
.CX 4144 4402,
.CX 4144 4401,
.CX 4144 4562,
.CX 4145 4563,
.CX 4145 4402,
.CCX 4563 4402 4403,
.CX 4145 4403,
.CX 4145 4402,
.CX 4145 4563,
.CX 4146 4564,
.CX 4146 4403,
.CCX 4564 4403 4404,
.CX 4146 4404,
.CX 4146 4403,
.CX 4146 4564,
.CX 4147 4565,
.CX 4147 4404,
.CCX 4565 4404 4405,
.CX 4147 4405,
.CX 4147 4404,
.CX 4147 4565,
.CX 4148 4566,
.CX 4148 4405,
.CCX 4566 4405 4406,
.CX 4148 4406,
.CX 4148 4405,
.CX 4148 4566,
.CX 4149 4567,
.CX 4149 4406,
.CCX 4567 4406 4407,
.CX 4149 4407,
.CX 4149 4406,
.CX 4149 4567,
.CX 4150 4568,
.CX 4150 4407,
.CCX 4568 4407 4408,
.CX 4150 4408,
.CX 4150 4407,
.CX 4150 4568,
.CX 4151 4569,
.CX 4151 4408,
.CCX 4569 4408 4409,
.CX 4151 4409,
.CX 4151 4408,
.CX 4151 4569,
.CX 4152 4570,
.CX 4152 4409,
.CCX 4570 4409 4410,
.CX 4152 4410,
.CX 4152 4409,
.CX 4152 4570,
.CX 4153 4571,
.CX 4153 4410,
.CCX 4571 4410 4411,
.CX 4153 4411,
.CX 4153 4410,
.CX 4153 4571,
.CX 4154 4572,
.CX 4154 4411,
.CCX 4572 4411 4412,
.CX 4154 4412,
.CX 4154 4411,
.CX 4154 4572,
.CX 4155 4573,
.CX 4155 4412,
.CCX 4573 4412 4413,
.CX 4155 4413,
.CX 4155 4412,
.CX 4155 4573,
.CX 4156 4574,
.CX 4156 4413,
.CCX 4574 4413 4414,
.CX 4156 4414,
.CX 4156 4413,
.CX 4156 4574,
.CX 4157 4575,
.CX 4157 4414,
.CCX 4575 4414 4415,
.CX 4157 4415,
.CX 4157 4414,
.CX 4157 4575,
.CX 4158 4576,
.CX 4158 4415,
.CCX 4576 4415 4416,
.CX 4158 4416,
.CX 4158 4415,
.CX 4158 4576,
.CX 4159 4577
]
def chunk25 : Program := [
.CX 4159 4416,
.CCX 4577 4416 4417,
.CX 4159 4417,
.CX 4159 4416,
.CX 4159 4577,
.CX 4160 4578,
.CX 4160 4417,
.CCX 4578 4417 4418,
.CX 4160 4418,
.CX 4160 4417,
.CX 4160 4578,
.CX 4161 4579,
.CX 4161 4418,
.CCX 4579 4418 4419,
.CX 4161 4419,
.CX 4161 4418,
.CX 4161 4579,
.CX 4162 4580,
.CX 4162 4419,
.CCX 4580 4419 4420,
.CX 4162 4420,
.CX 4162 4419,
.CX 4162 4580,
.CX 4163 4581,
.CX 4163 4420,
.CCX 4581 4420 4421,
.CX 4163 4421,
.CX 4163 4420,
.CX 4163 4581,
.CX 4164 4582,
.CX 4164 4421,
.CCX 4582 4421 4422,
.CX 4164 4422,
.CX 4164 4421,
.CX 4164 4582,
.CX 4165 4583,
.CX 4165 4422,
.CCX 4583 4422 4423,
.CX 4165 4423,
.CX 4165 4422,
.CX 4165 4583,
.CX 4166 4584,
.CX 4166 4423,
.CCX 4584 4423 4424,
.CX 4166 4424,
.CX 4166 4423,
.CX 4166 4584,
.CX 4167 4585,
.CX 4167 4424,
.CCX 4585 4424 4425,
.CX 4167 4425,
.CX 4167 4424,
.CX 4167 4585,
.CX 4168 4586,
.CX 4168 4425,
.CCX 4586 4425 4426,
.CX 4168 4426,
.CX 4168 4425,
.CX 4168 4586,
.CX 4169 4587,
.CX 4169 4426,
.CCX 4587 4426 4427,
.CX 4169 4427,
.CX 4169 4426,
.CX 4169 4587,
.CX 4170 4588,
.CX 4170 4427,
.CCX 4588 4427 4428,
.CX 4170 4428,
.CX 4170 4427,
.CX 4170 4588,
.CX 4171 4589,
.CX 4171 4428,
.CCX 4589 4428 4429,
.CX 4171 4429,
.CX 4171 4428,
.CX 4171 4589,
.CX 4172 4590,
.CX 4172 4429,
.CCX 4590 4429 4430,
.CX 4172 4430,
.CX 4172 4429,
.CX 4172 4590,
.CX 4173 4591,
.CX 4173 4430,
.CCX 4591 4430 4431,
.CX 4173 4431,
.CX 4173 4430,
.CX 4173 4591,
.CX 4174 4592,
.CX 4174 4431,
.CCX 4592 4431 4432,
.CX 4174 4432,
.CX 4174 4431,
.CX 4174 4592,
.CX 4175 4593,
.CX 4175 4432,
.CCX 4593 4432 4433,
.CX 4175 4433,
.CX 4175 4432,
.CX 4175 4593,
.CX 4176 4594,
.CX 4176 4433,
.CCX 4594 4433 4434,
.CX 4176 4434,
.CX 4176 4433,
.CX 4176 4594,
.CX 4177 4595,
.CX 4177 4434,
.CCX 4595 4434 4435,
.CX 4177 4435,
.CX 4177 4434,
.CX 4177 4595,
.CX 4178 4596,
.CX 4178 4435,
.CCX 4596 4435 4436,
.CX 4178 4436,
.CX 4178 4435,
.CX 4178 4596,
.CX 4179 4597,
.CX 4179 4436,
.CCX 4597 4436 4437,
.CX 4179 4437,
.CX 4179 4436,
.CX 4179 4597,
.CX 4180 4598,
.CX 4180 4437,
.CCX 4598 4437 4438
]
def chunk26 : Program := [
.CX 4180 4438,
.CX 4180 4437,
.CX 4180 4598,
.CX 4181 4599,
.CX 4181 4438,
.CCX 4599 4438 4439,
.CX 4181 4439,
.CX 4181 4438,
.CX 4181 4599,
.CX 4182 4600,
.CX 4182 4439,
.CCX 4600 4439 4440,
.CX 4182 4440,
.CX 4182 4439,
.CX 4182 4600,
.CX 4183 4601,
.CX 4183 4440,
.CCX 4601 4440 4441,
.CX 4183 4441,
.CX 4183 4440,
.CX 4183 4601,
.CX 4184 4602,
.CX 4184 4441,
.CCX 4602 4441 4442,
.CX 4184 4442,
.CX 4184 4441,
.CX 4184 4602,
.CX 4185 4603,
.CX 4185 4442,
.CCX 4603 4442 4443,
.CX 4185 4443,
.CX 4185 4442,
.CX 4185 4603,
.CX 4186 4604,
.CX 4186 4443,
.CCX 4604 4443 4444,
.CX 4186 4444,
.CX 4186 4443,
.CX 4186 4604,
.CX 4187 4605,
.CX 4187 4444,
.CCX 4605 4444 4445,
.CX 4187 4445,
.CX 4187 4444,
.CX 4187 4605,
.CX 4188 4606,
.CX 4188 4445,
.CCX 4606 4445 4446,
.CX 4188 4446,
.CX 4188 4445,
.CX 4188 4606,
.CX 4189 4607,
.CX 4189 4446,
.CCX 4607 4446 4447,
.CX 4189 4447,
.CX 4189 4446,
.CX 4189 4607,
.CX 4190 4608,
.CX 4190 4447,
.CCX 4608 4447 4448,
.CX 4190 4448,
.CX 4190 4447,
.CX 4190 4608,
.CX 4191 4609,
.CX 4191 4448,
.CCX 4609 4448 4449,
.CX 4191 4449,
.CX 4191 4448,
.CX 4191 4609,
.CX 4192 4610,
.CX 4192 4449,
.CCX 4610 4449 4450,
.CX 4192 4450,
.CX 4192 4449,
.CX 4192 4610,
.CX 4193 4611,
.CX 4193 4450,
.CCX 4611 4450 4451,
.CX 4193 4451,
.CX 4193 4450,
.CX 4193 4611,
.CX 4194 4612,
.CX 4194 4451,
.CCX 4612 4451 4452,
.CX 4194 4452,
.CX 4194 4451,
.CX 4194 4612,
.CX 4195 4613,
.CX 4195 4452,
.CCX 4613 4452 4453,
.CX 4195 4453,
.CX 4195 4452,
.CX 4195 4613,
.CX 4196 4614,
.CX 4196 4453,
.CCX 4614 4453 4454,
.CX 4196 4454,
.CX 4196 4453,
.CX 4196 4614,
.CX 4197 4615,
.CX 4197 4454,
.CCX 4615 4454 4455,
.CX 4197 4455,
.CX 4197 4454,
.CX 4197 4615,
.CX 4198 4616,
.CX 4198 4455,
.CCX 4616 4455 4456,
.CX 4198 4456,
.CX 4198 4455,
.CX 4198 4616,
.CX 4199 4617,
.CX 4199 4456,
.CCX 4617 4456 4457,
.CX 4199 4457,
.CX 4199 4456,
.CX 4199 4617,
.CX 4200 4618,
.CX 4200 4457,
.CCX 4618 4457 4458,
.CX 4200 4458,
.CX 4200 4457,
.CX 4200 4618,
.CX 4201 4619,
.CX 4201 4458,
.CCX 4619 4458 4459,
.CX 4201 4459,
.CX 4201 4458
]
def chunk27 : Program := [
.CX 4201 4619,
.CX 4202 4620,
.CX 4202 4459,
.CCX 4620 4459 4460,
.CX 4202 4460,
.CX 4202 4459,
.CX 4202 4620,
.CX 4203 4621,
.CX 4203 4460,
.CCX 4621 4460 4461,
.CX 4203 4461,
.CX 4203 4460,
.CX 4203 4621,
.CX 4204 4622,
.CX 4204 4461,
.CCX 4622 4461 4462,
.CX 4204 4462,
.CX 4204 4461,
.CX 4204 4622,
.CX 4205 4623,
.CX 4205 4462,
.CCX 4623 4462 4463,
.CX 4205 4463,
.CX 4205 4462,
.CX 4205 4623,
.CX 4206 4624,
.CX 4206 4463,
.CCX 4624 4463 4464,
.CX 4206 4464,
.CX 4206 4463,
.CX 4206 4624,
.CX 4207 4625,
.CX 4207 4464,
.CCX 4625 4464 4465,
.CX 4207 4465,
.CX 4207 4464,
.CX 4207 4625,
.CX 4208 4626,
.CX 4208 4465,
.CCX 4626 4465 4466,
.CX 4208 4466,
.CX 4208 4465,
.CX 4208 4626,
.CX 4209 4627,
.CX 4209 4466,
.CCX 4627 4466 4467,
.CX 4209 4467,
.CX 4209 4466,
.CX 4209 4627,
.CX 4210 4628,
.CX 4210 4467,
.CCX 4628 4467 4468,
.CX 4210 4468,
.CX 4210 4467,
.CX 4210 4628,
.CX 4211 4629,
.CX 4211 4468,
.CCX 4629 4468 4469,
.CX 4211 4469,
.CX 4211 4468,
.CX 4211 4629,
.CX 4212 4630,
.CX 4212 4469,
.CCX 4630 4469 4470,
.CX 4212 4470,
.CX 4212 4469,
.CX 4212 4630,
.CX 4213 4631,
.CX 4213 4470,
.CCX 4631 4470 4471,
.CX 4213 4471,
.CX 4213 4470,
.CX 4213 4631,
.CX 4214 4632,
.CX 4214 4471,
.CCX 4632 4471 4472,
.CX 4214 4472,
.CX 4214 4471,
.CX 4214 4632,
.CX 4215 4633,
.CX 4215 4472,
.CCX 4633 4472 4473,
.CX 4215 4473,
.CX 4215 4472,
.CX 4215 4633,
.CX 4216 4634,
.CX 4216 4473,
.CCX 4634 4473 4474,
.CX 4216 4474,
.CX 4216 4473,
.CX 4216 4634,
.CX 4217 4635,
.CX 4217 4474,
.CCX 4635 4474 4475,
.CX 4217 4475,
.CX 4217 4474,
.CX 4217 4635,
.CX 4218 4636,
.CX 4218 4475,
.CCX 4636 4475 4476,
.CX 4218 4476,
.CX 4218 4475,
.CX 4218 4636,
.CX 4219 4637,
.CX 4219 4476,
.CCX 4637 4476 4477,
.CX 4219 4477,
.CX 4219 4476,
.CX 4219 4637,
.CX 4220 4638,
.CX 4220 4477,
.CCX 4638 4477 4478,
.CX 4220 4478,
.CX 4220 4477,
.CX 4220 4638,
.CX 4221 4639,
.CX 4221 4478,
.CCX 4639 4478 4479,
.CX 4221 4479,
.CX 4221 4478,
.CX 4221 4639,
.CX 4222 4640,
.CX 4222 4479,
.CCX 4640 4479 4480,
.CX 4222 4480,
.CX 4222 4479,
.CX 4222 4640,
.CX 4223 4641
]
def chunk28 : Program := [
.CX 4223 4480,
.CCX 4641 4480 4481,
.CX 4223 4481,
.CX 4223 4480,
.CX 4223 4641,
.CX 4224 4642,
.CX 4224 4481,
.CCX 4642 4481 4482,
.CX 4224 4482,
.CX 4224 4481,
.CX 4224 4642,
.CX 4225 4643,
.CX 4225 4482,
.CCX 4643 4482 4483,
.CX 4225 4483,
.CX 4225 4482,
.CX 4225 4643,
.CX 4226 4644,
.CX 4226 4483,
.CCX 4644 4483 4484,
.CX 4226 4484,
.CX 4226 4483,
.CX 4226 4644,
.CX 4227 4645,
.CX 4227 4484,
.CCX 4645 4484 4485,
.CX 4227 4485,
.CX 4227 4484,
.CX 4227 4645,
.CX 4228 4646,
.CX 4228 4485,
.CCX 4646 4485 4486,
.CX 4228 4486,
.CX 4228 4485,
.CX 4228 4646,
.CX 4229 4647,
.CX 4229 4486,
.CCX 4647 4486 4487,
.CX 4229 4487,
.CX 4229 4486,
.CX 4229 4647,
.CX 4230 4648,
.CX 4230 4487,
.CCX 4648 4487 4488,
.CX 4230 4488,
.CX 4230 4487,
.CX 4230 4648,
.CX 4231 4649,
.CX 4231 4488,
.CCX 4649 4488 4489,
.CX 4231 4489,
.CX 4231 4488,
.CX 4231 4649,
.CX 4232 4650,
.CX 4232 4489,
.CCX 4650 4489 4490,
.CX 4232 4490,
.CX 4232 4489,
.CX 4232 4650,
.CX 4233 4651,
.CX 4233 4490,
.CCX 4651 4490 4491,
.CX 4233 4491,
.CX 4233 4490,
.CX 4233 4651,
.CX 4234 4652,
.CX 4234 4491,
.CCX 4652 4491 4492,
.CX 4234 4492,
.CX 4234 4491,
.CX 4234 4652,
.CX 4235 4653,
.CX 4235 4492,
.CCX 4653 4492 4493,
.CX 4235 4493,
.CX 4235 4492,
.CX 4235 4653,
.CX 4236 4654,
.CX 4236 4493,
.CCX 4654 4493 4494,
.CX 4236 4494,
.CX 4236 4493,
.CX 4236 4654,
.CX 4237 4655,
.CX 4237 4494,
.CCX 4655 4494 4495,
.CX 4237 4495,
.CX 4237 4494,
.CX 4237 4655,
.CX 4238 4656,
.CX 4238 4495,
.CCX 4656 4495 4496,
.CX 4238 4496,
.CX 4238 4495,
.CX 4238 4656,
.CX 4239 4657,
.CX 4239 4496,
.CCX 4657 4496 4497,
.CX 4239 4497,
.CX 4239 4496,
.CX 4239 4657,
.CX 4240 4658,
.CX 4240 4497,
.CCX 4658 4497 4498,
.CX 4240 4498,
.CX 4240 4497,
.CX 4240 4658,
.CX 4241 4659,
.CX 4241 4498,
.CCX 4659 4498 4499,
.CX 4241 4499,
.CX 4241 4498,
.CX 4241 4659,
.CX 4242 4660,
.CX 4242 4499,
.CCX 4660 4499 4500,
.CX 4242 4500,
.CX 4242 4499,
.CX 4242 4660,
.CX 4371 4661,
.CX 4371 4500,
.CCX 4661 4500 4764,
.CX 4371 4764,
.CX 4371 4500,
.CX 4371 4661,
.CX 4372 4662,
.CX 4372 4764,
.CCX 4662 4764 4765
]
def program : Program := ((((chunk0++(chunk1++chunk2))++((chunk3++chunk4)++(chunk5++chunk6)))++((chunk7++(chunk8++chunk9))++((chunk10++chunk11)++(chunk12++chunk13))))++(((chunk14++(chunk15++chunk16))++((chunk17++chunk18)++(chunk19++chunk20)))++(((chunk21++chunk22)++(chunk23++chunk24))++((chunk25++chunk26)++(chunk27++chunk28)))))
theorem length : program.length=3712 := by decide +kernel
attribute [local irreducible] program prefixState
theorem initial (b : BasisState) (q : Wire) : prefixState program 0 b q=b q := by simp only [prefixState,List.take_zero,basisRun]
theorem nw_4113_0_128 : noWriteBetween program 0 128 4113=true := by decide +kernel
theorem frame_4113_0_128 (b : BasisState) : prefixState program 128 b 4113=prefixState program 0 b 4113 := at_between program 0 128 4113 (by decide +kernel) nw_4113_0_128 b
theorem nw_4371_0_128 : noWriteBetween program 0 128 4371=true := by decide +kernel
theorem frame_4371_0_128 (b : BasisState) : prefixState program 128 b 4371=prefixState program 0 b 4371 := at_between program 0 128 4371 (by decide +kernel) nw_4371_0_128 b
theorem nw_4371_129_1056 : noWriteBetween program 129 1056 4371=true := by decide +kernel
theorem frame_4371_129_1056 (b : BasisState) : prefixState program 1056 b 4371=prefixState program 129 b 4371 := at_between program 129 1056 4371 (by decide +kernel) nw_4371_129_1056 b
theorem nw_4371_129_1059 : noWriteBetween program 129 1059 4371=true := by decide +kernel
theorem frame_4371_129_1059 (b : BasisState) : prefixState program 1059 b 4371=prefixState program 129 b 4371 := at_between program 129 1059 4371 (by decide +kernel) nw_4371_129_1059 b
theorem nw_4371_129_3703 : noWriteBetween program 129 3703 4371=true := by decide +kernel
theorem frame_4371_129_3703 (b : BasisState) : prefixState program 3703 b 4371=prefixState program 129 b 4371 := at_between program 129 3703 4371 (by decide +kernel) nw_4371_129_3703 b
theorem nw_4371_129_3706 : noWriteBetween program 129 3706 4371=true := by decide +kernel
theorem frame_4371_129_3706 (b : BasisState) : prefixState program 3706 b 4371=prefixState program 129 b 4371 := at_between program 129 3706 4371 (by decide +kernel) nw_4371_129_3706 b
theorem nw_4372_0_1062 : noWriteBetween program 0 1062 4372=true := by decide +kernel
theorem frame_4372_0_1062 (b : BasisState) : prefixState program 1062 b 4372=prefixState program 0 b 4372 := at_between program 0 1062 4372 (by decide +kernel) nw_4372_0_1062 b
theorem nw_4372_0_1063 : noWriteBetween program 0 1063 4372=true := by decide +kernel
theorem frame_4372_0_1063 (b : BasisState) : prefixState program 1063 b 4372=prefixState program 0 b 4372 := at_between program 0 1063 4372 (by decide +kernel) nw_4372_0_1063 b
theorem nw_4372_0_3709 : noWriteBetween program 0 3709 4372=true := by decide +kernel
theorem frame_4372_0_3709 (b : BasisState) : prefixState program 3709 b 4372=prefixState program 0 b 4372 := at_between program 0 3709 4372 (by decide +kernel) nw_4372_0_3709 b
theorem nw_4372_0_3710 : noWriteBetween program 0 3710 4372=true := by decide +kernel
theorem frame_4372_0_3710 (b : BasisState) : prefixState program 3710 b 4372=prefixState program 0 b 4372 := at_between program 0 3710 4372 (by decide +kernel) nw_4372_0_3710 b
theorem nw_4639_0_263 : noWriteBetween program 0 263 4639=true := by decide +kernel
theorem frame_4639_0_263 (b : BasisState) : prefixState program 263 b 4639=prefixState program 0 b 4639 := at_between program 0 263 4639 (by decide +kernel) nw_4639_0_263 b
theorem nw_4639_264_1056 : noWriteBetween program 264 1056 4639=true := by decide +kernel
theorem frame_4639_264_1056 (b : BasisState) : prefixState program 1056 b 4639=prefixState program 264 b 4639 := at_between program 264 1056 4639 (by decide +kernel) nw_4639_264_1056 b
theorem nw_4639_1057_1058 : noWriteBetween program 1057 1058 4639=true := by decide +kernel
theorem frame_4639_1057_1058 (b : BasisState) : prefixState program 1058 b 4639=prefixState program 1057 b 4639 := at_between program 1057 1058 4639 (by decide +kernel) nw_4639_1057_1058 b
theorem nw_4640_0_264 : noWriteBetween program 0 264 4640=true := by decide +kernel
theorem frame_4640_0_264 (b : BasisState) : prefixState program 264 b 4640=prefixState program 0 b 4640 := at_between program 0 264 4640 (by decide +kernel) nw_4640_0_264 b
theorem nw_4640_265_1062 : noWriteBetween program 265 1062 4640=true := by decide +kernel
theorem frame_4640_265_1062 (b : BasisState) : prefixState program 1062 b 4640=prefixState program 265 b 4640 := at_between program 265 1062 4640 (by decide +kernel) nw_4640_265_1062 b
theorem nw_4640_1063_1064 : noWriteBetween program 1063 1064 4640=true := by decide +kernel
theorem frame_4640_1063_1064 (b : BasisState) : prefixState program 1064 b 4640=prefixState program 1063 b 4640 := at_between program 1063 1064 4640 (by decide +kernel) nw_4640_1063_1064 b
theorem nw_4661_0_285 : noWriteBetween program 0 285 4661=true := by decide +kernel
theorem frame_4661_0_285 (b : BasisState) : prefixState program 285 b 4661=prefixState program 0 b 4661 := at_between program 0 285 4661 (by decide +kernel) nw_4661_0_285 b
theorem nw_4661_286_3703 : noWriteBetween program 286 3703 4661=true := by decide +kernel
theorem frame_4661_286_3703 (b : BasisState) : prefixState program 3703 b 4661=prefixState program 286 b 4661 := at_between program 286 3703 4661 (by decide +kernel) nw_4661_286_3703 b
theorem nw_4661_3704_3705 : noWriteBetween program 3704 3705 4661=true := by decide +kernel
theorem frame_4661_3704_3705 (b : BasisState) : prefixState program 3705 b 4661=prefixState program 3704 b 4661 := at_between program 3704 3705 4661 (by decide +kernel) nw_4661_3704_3705 b
theorem nw_4662_0_286 : noWriteBetween program 0 286 4662=true := by decide +kernel
theorem frame_4662_0_286 (b : BasisState) : prefixState program 286 b 4662=prefixState program 0 b 4662 := at_between program 0 286 4662 (by decide +kernel) nw_4662_0_286 b
theorem nw_4662_287_3709 : noWriteBetween program 287 3709 4662=true := by decide +kernel
theorem frame_4662_287_3709 (b : BasisState) : prefixState program 3709 b 4662=prefixState program 287 b 4662 := at_between program 287 3709 4662 (by decide +kernel) nw_4662_287_3709 b
theorem nw_4662_3710_3711 : noWriteBetween program 3710 3711 4662=true := by decide +kernel
theorem frame_4662_3710_3711 (b : BasisState) : prefixState program 3711 b 4662=prefixState program 3710 b 4662 := at_between program 3710 3711 4662 (by decide +kernel) nw_4662_3710_3711 b
theorem nw_4701_0_263 : noWriteBetween program 0 263 4701=true := by decide +kernel
theorem frame_4701_0_263 (b : BasisState) : prefixState program 263 b 4701=prefixState program 0 b 4701 := at_between program 0 263 4701 (by decide +kernel) nw_4701_0_263 b
theorem nw_4702_0_264 : noWriteBetween program 0 264 4702=true := by decide +kernel
theorem frame_4702_0_264 (b : BasisState) : prefixState program 264 b 4702=prefixState program 0 b 4702 := at_between program 0 264 4702 (by decide +kernel) nw_4702_0_264 b
theorem nw_4723_0_285 : noWriteBetween program 0 285 4723=true := by decide +kernel
theorem frame_4723_0_285 (b : BasisState) : prefixState program 285 b 4723=prefixState program 0 b 4723 := at_between program 0 285 4723 (by decide +kernel) nw_4723_0_285 b
theorem nw_4724_0_286 : noWriteBetween program 0 286 4724=true := by decide +kernel
theorem frame_4724_0_286 (b : BasisState) : prefixState program 286 b 4724=prefixState program 0 b 4724 := at_between program 0 286 4724 (by decide +kernel) nw_4724_0_286 b
theorem nw_4764_0_1058 : noWriteBetween program 0 1058 4764=true := by decide +kernel
theorem frame_4764_0_1058 (b : BasisState) : prefixState program 1058 b 4764=prefixState program 0 b 4764 := at_between program 0 1058 4764 (by decide +kernel) nw_4764_0_1058 b
theorem nw_4764_1060_1063 : noWriteBetween program 1060 1063 4764=true := by decide +kernel
theorem frame_4764_1060_1063 (b : BasisState) : prefixState program 1063 b 4764=prefixState program 1060 b 4764 := at_between program 1060 1063 4764 (by decide +kernel) nw_4764_1060_1063 b
theorem nw_4764_2414_3705 : noWriteBetween program 2414 3705 4764=true := by decide +kernel
theorem frame_4764_2414_3705 (b : BasisState) : prefixState program 3705 b 4764=prefixState program 2414 b 4764 := at_between program 2414 3705 4764 (by decide +kernel) nw_4764_2414_3705 b
theorem nw_4764_3707_3710 : noWriteBetween program 3707 3710 4764=true := by decide +kernel
theorem frame_4764_3707_3710 (b : BasisState) : prefixState program 3710 b 4764=prefixState program 3707 b 4764 := at_between program 3707 3710 4764 (by decide +kernel) nw_4764_3707_3710 b
theorem gate_128 : program[128]'(by rw [length];decide +kernel)=.CX 4113 4371 := by decide +kernel
theorem step_128 (b : BasisState) : prefixState program 129 b 4371=((prefixState program 0 b 4371) ^^ (prefixState program 0 b 4113)) := by
 have h:=congrFun (at_succ program 128 (by rw [length];decide +kernel) b) 4371
 rw [gate_128] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4113_0_128 b,frame_4371_0_128 b] at h
 exact h
theorem gate_263 : program[263]'(by rw [length];decide +kernel)=.CX 4701 4639 := by decide +kernel
theorem step_263 (b : BasisState) : prefixState program 264 b 4639=((prefixState program 0 b 4639) ^^ (prefixState program 0 b 4701)) := by
 have h:=congrFun (at_succ program 263 (by rw [length];decide +kernel) b) 4639
 rw [gate_263] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4639_0_263 b,frame_4701_0_263 b] at h
 exact h
theorem gate_264 : program[264]'(by rw [length];decide +kernel)=.CX 4702 4640 := by decide +kernel
theorem step_264 (b : BasisState) : prefixState program 265 b 4640=((prefixState program 0 b 4640) ^^ (prefixState program 0 b 4702)) := by
 have h:=congrFun (at_succ program 264 (by rw [length];decide +kernel) b) 4640
 rw [gate_264] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4640_0_264 b,frame_4702_0_264 b] at h
 exact h
theorem gate_285 : program[285]'(by rw [length];decide +kernel)=.CX 4723 4661 := by decide +kernel
theorem step_285 (b : BasisState) : prefixState program 286 b 4661=((prefixState program 0 b 4661) ^^ (prefixState program 0 b 4723)) := by
 have h:=congrFun (at_succ program 285 (by rw [length];decide +kernel) b) 4661
 rw [gate_285] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4661_0_285 b,frame_4723_0_285 b] at h
 exact h
theorem gate_286 : program[286]'(by rw [length];decide +kernel)=.CX 4724 4662 := by decide +kernel
theorem step_286 (b : BasisState) : prefixState program 287 b 4662=((prefixState program 0 b 4662) ^^ (prefixState program 0 b 4724)) := by
 have h:=congrFun (at_succ program 286 (by rw [length];decide +kernel) b) 4662
 rw [gate_286] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4662_0_286 b,frame_4724_0_286 b] at h
 exact h
theorem gate_1056 : program[1056]'(by rw [length];decide +kernel)=.CX 4371 4639 := by decide +kernel
theorem step_1056 (b : BasisState) : prefixState program 1057 b 4639=((prefixState program 264 b 4639) ^^ (prefixState program 129 b 4371)) := by
 have h:=congrFun (at_succ program 1056 (by rw [length];decide +kernel) b) 4639
 rw [gate_1056] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4371_129_1056 b,frame_4639_264_1056 b] at h
 exact h
theorem gate_1058 : program[1058]'(by rw [length];decide +kernel)=.CCX 4639 4500 4764 := by decide +kernel
theorem step_1058 (b : BasisState) : prefixState program 1059 b 4764=((prefixState program 0 b 4764) ^^ ((prefixState program 1057 b 4639) && (prefixState program 1058 b 4500))) := by
 have h:=congrFun (at_succ program 1058 (by rw [length];decide +kernel) b) 4764
 rw [gate_1058] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4639_1057_1058 b,frame_4764_0_1058 b] at h
 exact h
theorem gate_1059 : program[1059]'(by rw [length];decide +kernel)=.CX 4371 4764 := by decide +kernel
theorem step_1059 (b : BasisState) : prefixState program 1060 b 4764=((prefixState program 1059 b 4764) ^^ (prefixState program 129 b 4371)) := by
 have h:=congrFun (at_succ program 1059 (by rw [length];decide +kernel) b) 4764
 rw [gate_1059] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4371_129_1059 b] at h
 exact h
theorem gate_1062 : program[1062]'(by rw [length];decide +kernel)=.CX 4372 4640 := by decide +kernel
theorem step_1062 (b : BasisState) : prefixState program 1063 b 4640=((prefixState program 265 b 4640) ^^ (prefixState program 0 b 4372)) := by
 have h:=congrFun (at_succ program 1062 (by rw [length];decide +kernel) b) 4640
 rw [gate_1062] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4372_0_1062 b,frame_4640_265_1062 b] at h
 exact h
theorem gate_1063 : program[1063]'(by rw [length];decide +kernel)=.CX 4372 4764 := by decide +kernel
theorem step_1063 (b : BasisState) : prefixState program 1064 b 4764=((prefixState program 1060 b 4764) ^^ (prefixState program 0 b 4372)) := by
 have h:=congrFun (at_succ program 1063 (by rw [length];decide +kernel) b) 4764
 rw [gate_1063] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4372_0_1063 b,frame_4764_1060_1063 b] at h
 exact h
theorem gate_2413 : program[2413]'(by rw [length];decide +kernel)=.measureX 4764 [] [.CZ 4371 4635,.CZ 4371 4500,.CZ 4635 4500] := by decide +kernel
theorem step_2413 (b : BasisState) : prefixState program 2414 b 4764=(false) := by
 have h:=congrFun (at_succ program 2413 (by rw [length];decide +kernel) b) 4764
 rw [gate_2413] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h
theorem gate_3703 : program[3703]'(by rw [length];decide +kernel)=.CX 4371 4661 := by decide +kernel
theorem step_3703 (b : BasisState) : prefixState program 3704 b 4661=((prefixState program 286 b 4661) ^^ (prefixState program 129 b 4371)) := by
 have h:=congrFun (at_succ program 3703 (by rw [length];decide +kernel) b) 4661
 rw [gate_3703] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4371_129_3703 b,frame_4661_286_3703 b] at h
 exact h
theorem gate_3705 : program[3705]'(by rw [length];decide +kernel)=.CCX 4661 4500 4764 := by decide +kernel
theorem step_3705 (b : BasisState) : prefixState program 3706 b 4764=((prefixState program 2414 b 4764) ^^ ((prefixState program 3704 b 4661) && (prefixState program 3705 b 4500))) := by
 have h:=congrFun (at_succ program 3705 (by rw [length];decide +kernel) b) 4764
 rw [gate_3705] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4661_3704_3705 b,frame_4764_2414_3705 b] at h
 exact h
theorem gate_3706 : program[3706]'(by rw [length];decide +kernel)=.CX 4371 4764 := by decide +kernel
theorem step_3706 (b : BasisState) : prefixState program 3707 b 4764=((prefixState program 3706 b 4764) ^^ (prefixState program 129 b 4371)) := by
 have h:=congrFun (at_succ program 3706 (by rw [length];decide +kernel) b) 4764
 rw [gate_3706] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4371_129_3706 b] at h
 exact h
theorem gate_3709 : program[3709]'(by rw [length];decide +kernel)=.CX 4372 4662 := by decide +kernel
theorem step_3709 (b : BasisState) : prefixState program 3710 b 4662=((prefixState program 287 b 4662) ^^ (prefixState program 0 b 4372)) := by
 have h:=congrFun (at_succ program 3709 (by rw [length];decide +kernel) b) 4662
 rw [gate_3709] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4372_0_3709 b,frame_4662_287_3709 b] at h
 exact h
theorem gate_3710 : program[3710]'(by rw [length];decide +kernel)=.CX 4372 4764 := by decide +kernel
theorem step_3710 (b : BasisState) : prefixState program 3711 b 4764=((prefixState program 3707 b 4764) ^^ (prefixState program 0 b 4372)) := by
 have h:=congrFun (at_succ program 3710 (by rw [length];decide +kernel) b) 4764
 rw [gate_3710] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4372_0_3710 b,frame_4764_3707_3710 b] at h
 exact h
end ECDSAAdd.Entrant.LocalEFoldTrace

end

section
-- Preserved checked proof component: LocalEFoldRelations
namespace ECDSAAdd.Entrant.LocalEFoldRelations
open ECDSAAdd SixCarryTrace SixCarryFrame LocalEFoldTrace
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] LocalEFoldTrace.program prefixState
theorem relation1064 (b : BasisState)
 (hz : ∀q∈[4639, 4701, 4640, 4702, 4764, 4661, 4723, 4662, 4724],b q=false)
 (hc : (b 4372 && (b 4371 ^^ b 4113))=false) :
 ((prefixState program 1064 b 4640) && (prefixState program 1064 b 4764))=
 prefixState program 1064 b 4640 := by
 have z4639 := hz 4639 (by decide +kernel)
 have z4701 := hz 4701 (by decide +kernel)
 have z4640 := hz 4640 (by decide +kernel)
 have z4702 := hz 4702 (by decide +kernel)
 have z4764 := hz 4764 (by decide +kernel)
 have z4661 := hz 4661 (by decide +kernel)
 have z4723 := hz 4723 (by decide +kernel)
 have z4662 := hz 4662 (by decide +kernel)
 have z4724 := hz 4724 (by decide +kernel)
 simp only [frame_4640_1063_1064,step_128,step_263,step_264,step_1056,step_1058,step_1059,step_1062,step_1063,initial,z4639,z4701,z4640,z4702,z4764]
 cases hu : b 4371 <;> cases hc0 : b 4113 <;> cases hv : b 4372 <;> cases hx : prefixState program 1058 b 4500 <;> simp_all
#print axioms relation1064
theorem relation3711 (b : BasisState)
 (hz : ∀q∈[4639, 4701, 4640, 4702, 4764, 4661, 4723, 4662, 4724],b q=false)
 (hc : (b 4372 && (b 4371 ^^ b 4113))=false) :
 ((prefixState program 3711 b 4662) && (prefixState program 3711 b 4764))=
 prefixState program 3711 b 4662 := by
 have z4639 := hz 4639 (by decide +kernel)
 have z4701 := hz 4701 (by decide +kernel)
 have z4640 := hz 4640 (by decide +kernel)
 have z4702 := hz 4702 (by decide +kernel)
 have z4764 := hz 4764 (by decide +kernel)
 have z4661 := hz 4661 (by decide +kernel)
 have z4723 := hz 4723 (by decide +kernel)
 have z4662 := hz 4662 (by decide +kernel)
 have z4724 := hz 4724 (by decide +kernel)
 simp only [frame_4662_3710_3711,step_128,step_285,step_286,step_2413,step_3703,step_3705,step_3706,step_3709,step_3710,initial,z4661,z4723,z4662,z4724]
 cases hu : b 4371 <;> cases hc0 : b 4113 <;> cases hv : b 4372 <;> cases hx : prefixState program 3705 b 4500 <;> simp_all
#print axioms relation3711
end ECDSAAdd.Entrant.LocalEFoldRelations

end

section
-- Preserved checked proof component: LocalEFoldAnchor
namespace ECDSAAdd.Entrant.LocalEFoldAnchor
open ECDSAAdd SixCarryTrace SixCarryFrame
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
def actual : Program := ControlLoan1589BFFold.eFoldTq LowAccCarryDevelop.L LowAccCarryDevelop.c
theorem literal : actual.take 3712=LocalEFoldTrace.program := by
 apply ParkAProgramBool.programEq_sound
 decide +kernel
attribute [local irreducible] actual LocalEFoldTrace.program prefixState
theorem prefix_eq (n : Nat) (hn : n≤3712) (b : BasisState) :
 prefixState actual n b=prefixState LocalEFoldTrace.program n b := by
 have h:=congrArg (fun p : Program=>p.take n) literal
 simp only [List.take_take,Nat.min_eq_left hn] at h
 simpa only [prefixState] using congrArg (fun p : Program=>basisRun p b) h
#print axioms literal
end ECDSAAdd.Entrant.LocalEFoldAnchor

end

section
-- Preserved checked proof component: LocalEFoldOptimize
namespace ECDSAAdd.Entrant.LocalEFoldOptimize
open ECDSAAdd SixCarryTrace SixCarryFrame LocalEFoldAnchor SixCarryPatchGeneric
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] actual run prefixState
def Clean (b : BasisState) : Prop := ∀q∈[4639,4701,4640,4702,4764,4661,4723,4662,4724],b q=false
def Top (b : BasisState) : Prop := (b 4372 && (b 4371 ^^ b 4113))=false
def late : Program := patch actual 3711 [.CX 4662 4765]
def improved : Program := patch late 1064 [.CX 4640 4765]
attribute [local irreducible] late improved

theorem lookup (i : Nat) (hi : i<3712) : actual[i]?=LocalEFoldTrace.program[i]? := by
 have h:=congrArg (fun p : Program=>p[i]?) literal
 simpa only [List.getElem?_take_of_lt hi] using h

theorem gate1064 : actual[1064]?=some (.CCX 4640 4764 4765) :=
 (lookup 1064 (by decide +kernel)).trans (by decide +kernel)
theorem gate3711 : actual[3711]?=some (.CCX 4662 4764 4765) :=
 (lookup 3711 (by decide +kernel)).trans (by decide +kernel)

theorem local_gate (s : State) (m : List Bool) (a : Wire)
 (h : (s.basis a && s.basis 4764)=s.basis a) :
 run [.CCX a 4764 4765] m s=run [.CX a 4765] m s := by
 have hv:=congrArg (fun z=>s.basis 4765 ^^ z) h
 apply state_ext
 · simp [run]
 · funext q
   by_cases hq : q=4765
   · subst q
     simpa [run,writeBit,Function.update_apply] using hv
   · simp [run,writeBit,hq]

theorem condition1064 (b : BasisState) (hz : Clean b) (ht : Top b) :
 ((prefixState actual 1064 b 4640) && (prefixState actual 1064 b 4764))=
 prefixState actual 1064 b 4640 := by
 rw [prefix_eq 1064 (by decide +kernel)]
 exact LocalEFoldRelations.relation1064 b hz ht

theorem condition3711 (b : BasisState) (hz : Clean b) (ht : Top b) :
 ((prefixState actual 3711 b 4662) && (prefixState actual 3711 b 4764))=
 prefixState actual 3711 b 4662 := by
 rw [prefix_eq 3711 (by decide +kernel)]
 exact LocalEFoldRelations.relation3711 b hz ht

theorem late_eq (s : State) (m : List Bool) (hz : Clean s.basis) (ht : Top s.basis) :
 run actual m s=run late m s := by
 unfold late
 apply SixCarryPatchGeneric.run_eq actual 3711 4662 4764 4765 [.CX 4662 4765] gate3711 (by decide +kernel) s m
 apply local_gate
 simpa only [prefixState,run_basis] using condition3711 s.basis hz ht

theorem earlier_prefix : late.take 1064=actual.take 1064 := by
 unfold late
 exact SixCarryPatchPrefix.take_before actual 3711 (.CCX 4662 4764 4765) [.CX 4662 4765] 1064 gate3711 (by decide +kernel)

theorem earlier_lookup : late[1064]?=some (.CCX 4640 4764 4765) := by
 unfold late
 exact (SixCarryPatchPrefix.lookup_before actual 3711 (.CCX 4662 4764 4765) [.CX 4662 4765] 1064 gate3711 (by decide +kernel)).trans gate1064

theorem improved_eq (s : State) (m : List Bool) (hz : Clean s.basis) (ht : Top s.basis) :
 run actual m s=run improved m s := by
 apply (late_eq s m hz ht).trans
 unfold improved
 apply SixCarryPatchGeneric.run_eq late 1064 4640 4764 4765 [.CX 4640 4765] earlier_lookup (by decide +kernel) s m
 apply local_gate
 rw [earlier_prefix]
 simpa only [prefixState,run_basis] using condition1064 s.basis hz ht

#print axioms improved_eq
end ECDSAAdd.Entrant.LocalEFoldOptimize

end

section
-- Preserved checked proof component: LocalEFoldResources
namespace ECDSAAdd.Entrant.LocalEFoldResources
open ECDSAAdd Arithmetic Challenge LocalEFoldOptimize LocalEFoldAnchor SixCarryPatchGeneric
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] actual late improved toffoliCount measurementCount gateSlots wires

theorem late_shape : late=patch actual 3711 [.CX 4662 4765] := by unfold late;rfl
theorem improved_shape : improved=patch late 1064 [.CX 4640 4765] := by unfold improved;rfl

theorem toffoli : toffoliCount improved+2=toffoliCount actual := by
 have a:toffoliCount late+1=toffoliCount actual := by
  exact Eq.mp (congrArg (fun p : Program=>toffoliCount p+1=toffoliCount actual) late_shape.symm) (SixCarryPatchResources.toffoli actual 3711 4662 4764 4765 [.CX 4662 4765] gate3711 (by decide +kernel))
 have b:toffoliCount improved+1=toffoliCount late := by
  exact Eq.mp (congrArg (fun p : Program=>toffoliCount p+1=toffoliCount late) improved_shape.symm) (SixCarryPatchResources.toffoli late 1064 4640 4764 4765 [.CX 4640 4765] earlier_lookup (by decide +kernel))
 omega

theorem measurements : measurementCount improved=measurementCount actual := by
 have a:measurementCount late=measurementCount actual := by
  exact Eq.mp (congrArg (fun p : Program=>measurementCount p=measurementCount actual) late_shape.symm) (SixCarryPatchResources.measurements actual 3711 4662 4764 4765 [.CX 4662 4765] gate3711 (by decide +kernel))
 have b:measurementCount improved=measurementCount late := by
  exact Eq.mp (congrArg (fun p : Program=>measurementCount p=measurementCount late) improved_shape.symm) (SixCarryPatchResources.measurements late 1064 4640 4764 4765 [.CX 4640 4765] earlier_lookup (by decide +kernel))
 exact b.trans a

theorem slots : gateSlots improved=gateSlots actual := by
 have a:gateSlots late=gateSlots actual := by
  exact Eq.mp (congrArg (fun p : Program=>gateSlots p=gateSlots actual) late_shape.symm) (ExtraCarryResourceGeneric.patch_slots_zero actual 3711 4662 4764 4765 [.CX 4662 4765] gate3711 (by decide +kernel))
 have b:gateSlots improved=gateSlots late := by
  exact Eq.mp (congrArg (fun p : Program=>gateSlots p=gateSlots late) improved_shape.symm) (ExtraCarryResourceGeneric.patch_slots_zero late 1064 4640 4764 4765 [.CX 4640 4765] earlier_lookup (by decide +kernel))
 exact b.trans a

theorem repair_subset (p : Program) (i a b t : Nat) (hg : p[i]?=some (.CCX a b t)) :
 wires [.CX a t]⊆wires p := by
 rw [SixCarryReplace.old_shape_of_lookup p i (.CCX a b t) hg,wires_append,wires_append]
 intro q hq
 have small : wires [.CX a t]⊆wires [.CCX a b t] := by
  intro w hw
  simp [wires,Instr.wires] at hw ⊢
  tauto
 exact Finset.mem_union_right _ (Finset.mem_union_left _ (small hq))

theorem support : wires improved⊆wires actual := by
 have a:wires late⊆wires actual := by
  exact Eq.mp (congrArg (fun p : Program=>wires p⊆wires actual) late_shape.symm) (SixCarryPatchSupport.support actual 3711 (.CCX 4662 4764 4765) [.CX 4662 4765] gate3711 (repair_subset actual 3711 4662 4764 4765 gate3711))
 have b:wires improved⊆wires late := by
  exact Eq.mp (congrArg (fun p : Program=>wires p⊆wires late) improved_shape.symm) (SixCarryPatchSupport.support late 1064 (.CCX 4640 4764 4765) [.CX 4640 4765] earlier_lookup (repair_subset late 1064 4640 4764 4765 earlier_lookup))
 exact b.trans a

theorem physical (hp : GatePhysical actual) : GatePhysical improved := by
 have a:GatePhysical late := by
  exact Eq.mp (congrArg (fun p : Program=>GatePhysical p) late_shape.symm) (SixCarryPatchSupport.physical actual 3711 (.CCX 4662 4764 4765) [.CX 4662 4765] gate3711 hp (physicalGateCheck_correct _ (by decide +kernel)))
 exact Eq.mp (congrArg (fun p : Program=>GatePhysical p) improved_shape.symm) (SixCarryPatchSupport.physical late 1064 (.CCX 4640 4764 4765) [.CX 4640 4765] earlier_lookup a (physicalGateCheck_correct _ (by decide +kernel)))
#print axioms toffoli
#print axioms support
end ECDSAAdd.Entrant.LocalEFoldResources

end

section
-- Preserved checked proof component: LocalEFoldInputs
namespace ECDSAAdd.Entrant.LocalEFoldInputs
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open ControlLoan1589BFFold LocalEFoldOptimize
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
abbrev L := LowAccCarryDevelop.L

theorem clean (base b : BasisState) (O E : Nat) (hc : L.PairClean base)
 (h : BState L base O E 0 b) : Clean b := by
 have c:=bstate_clean L LowAccCarryDevelop.layout_nodup base hc O E b h
 have checked : ([4639,4701,4640,4702,4764,4661,4723,4662,4724] : List Wire).all
  (fun q=>decide (q∈L.core.work++L.foldPad))=true := by decide +kernel
 intro q hq
 have mem:=of_decide_eq_true (List.all_eq_true.mp checked q hq)
 rcases List.mem_append.mp mem with hw|hp
 · exact (regValue_zero _ _).mp c.work q hw
 · exact (regValue_zero _ _).mp c.pad q hp

theorem bit128 (b : BasisState) (E : Nat) (he : regValue (eReg L) b=E) :
 (b 4371).toNat=E/2^128%2 := by
 have h:=regValue_bit (eReg L) 128 0 b (by decide +kernel)
 rw [show (eReg L).getD 128 0=4371 from by decide +kernel,he] at h
 exact h

theorem bit129 (b : BasisState) (E : Nat) (he : regValue (eReg L) b=E) :
 (b 4372).toNat=E/2^129%2 := by
 have h:=regValue_bit (eReg L) 129 0 b (by decide +kernel)
 rw [show (eReg L).getD 129 0=4372 from by decide +kernel,he] at h
 exact h

theorem top (b : BasisState) (E : Nat) (he : regValue (eReg L) b=E)
 (hb : E<2^130) (hr : E<2^128 ∨ 2^130-2^128≤E)
 (hz : b 4113=false → E=0) : Top b := by
 have hu:=bit128 b E he
 have hv:=bit129 b E he
 by_cases hc : b 4113=false
 · have e:=hz hc
   have v:b 4372=false := by
    cases h:b 4372 <;> simp_all
   simp [LocalEFoldOptimize.Top,v]
 · have c:b 4113=true := by cases h:b 4113 <;> simp_all
   have eq:E/2^128%2=E/2^129%2 := by
    norm_num at hb hr ⊢
    omega
   have both : (b 4371).toNat=(b 4372).toNat := hu.trans (eq.trans hv.symm)
   have same : b 4371=b 4372 := by
    cases hU:b 4371 <;> cases hV:b 4372 <;> simp [hU,hV] at both ⊢
   unfold LocalEFoldOptimize.Top
   rw [same]
   cases hv0:b 4372 <;> simp [c]

theorem range (A B : Nat) (ha : A<2^128) (hb : B<2^128) :
 (A+2^130-B)%2^130<2^128 ∨ 2^130-2^128≤(A+2^130-B)%2^130 := by
 norm_num at ha hb ⊢
 omega

#print axioms top
#print axioms clean
end ECDSAAdd.Entrant.LocalEFoldInputs

end

section
-- Preserved checked proof component: LocalEFoldBody
namespace ECDSAAdd.Entrant.LocalEFoldBody
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop LowAccCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
def bodyForFold (L : CuccaroStreamedSquareWideLayout) (loop fold : Program) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldFor L loop ++ (fold ++ ParkCarry10Develop.rebuild L)))
theorem frame
 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (loopProgram : Program)
 (loopSpec : ∀ (base : BasisState) (_clean : L.PairClean base) (_hsum : base L.core.sumCarry=false)
  (O E O' : Nat),
  Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
   (BState L base O' E (4294968272*regValue (hiReg L) base)) →
  Triple (BState L base O E 0) loopProgram (BState L base O' E 0))
 (foldProgram : Program)
 (foldSpec : ∀ (base : BasisState) (_clean : L.PairClean base) (O E : Nat)
  (_hO : O<SquareReduction.p) (_hE : E<2^130)
  (_hRange : E<2^128 ∨ 2^130-2^128≤E)
  (_hOff : base c=false → E=0) (Q : BasisState→Prop),
  Triple (BState L base O E 0) (eFoldTq L c) Q →
  Triple (BState L base O E 0) foldProgram Q)
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyForFold L loopProgram foldProgram)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by

  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := ParkCarryDevelop.base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply ParkCarryDevelop.sumCarry_away L hn;simp [ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [ParkCarryDevelop.reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have source0:base (L.core.high.headD 0)=digit originalM 0:=by
    simpa only[digit,pow_zero,Nat.div_one]using head_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE2:(2^32*H+l'+2^128*K)%2=lowSum (base c) originalM u%2:=by omega
  have loanFact0:=LowBitCarryNumbers.loan0_from_mod2 (base c) originalM u (2^32*H+l'+2^128*K)
    (by simpa only[lowSum]using modE2)
  rw[←source0]at loanFact0
  have wm := wMidFullCCC0_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact0
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC0 L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have loop := loopSpec base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (foldFor L loopProgram) (BState L baseK O3 E1 0) :=
    by simpa only [foldFor,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
  have hA : 2^32*H+l'<2^128 := by
    have hH0:=hH
    have hl0:=hl'
    norm_num at hH0 hl0 ⊢
    omega
  have hEbound : E1<2^130 := Nat.mod_lt _ (by positivity)
  have hErange : E1<2^128 ∨ 2^130-2^128≤E1 :=
    LocalEFoldInputs.range (2^32*H+l') b1 hA hb1lt
  have hEoff : baseK c=false → E1=0 := by
    intro hc0
    have m0 : M=0 := hg (gc.symm.trans hc0)
    simp [E1,H,l',b0,b1,P,u,m0]
  have tfNew : Triple (BState L baseK O3 E1 0) foldProgram (BState L baseK O4 E1 0) :=
    foldSpec baseK hcK O3 E1 hO3 hEbound hErange hEoff _ tf
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=ParkCarryDevelop.restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (ParkCarry10Develop.rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv0 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tfNew.seq tr)) conv0))
  rw [key] at all
  simpa only [bodyForFold] using all


#print axioms frame
end ECDSAAdd.Entrant.LocalEFoldBody

end

section
-- Preserved checked proof component: LocalEFoldLift
namespace ECDSAAdd.Entrant.LocalEFoldLift
open ECDSAAdd Arithmetic ControlLoan1589BFFold LocalEFoldOptimize LocalEFoldAnchor
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
abbrev L := LowAccCarryDevelop.L

theorem transfer (base : BasisState) (clean : L.PairClean base) (O E : Nat)
 (hb : E<2^130) (hr : E<2^128 ∨ 2^130-2^128≤E)
 (hoff : base 4113=false → E=0) (Q : BasisState→Prop)
 (old : Triple (BState L base O E 0) (eFoldTq L LowAccCarryDevelop.c) Q) :
 Triple (BState L base O E 0) improved Q := by
 intro s m hs
 have c:s.basis 4113=base 4113 := hs.2.2.2 4113 (by decide +kernel) (by decide +kernel) (by decide +kernel)
 have hz:=LocalEFoldInputs.clean base s.basis O E clean hs
 have ht:=LocalEFoldInputs.top s.basis E hs.2.1 hb hr (fun hc=>hoff (c.symm.trans hc))
 have eq:=improved_eq s m hz ht
 rw [←eq]
 simpa only [actual] using old s m hs
#print axioms transfer
end ECDSAAdd.Entrant.LocalEFoldLift

end

section
-- Preserved checked proof component: LocalEFoldBody90
namespace ECDSAAdd.Entrant.LocalEFoldBody90
open ECDSAAdd Arithmetic Challenge ControlLoan1589BFFold
open LocalEFoldOptimize LocalEFoldAnchor LocalEFoldBody
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
abbrev L := LowAccCarryDevelop.L
abbrev c := LowAccCarryDevelop.c
def bodyWith (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c)) : Program :=
 bodyForFold L (LowAccCarryDevelop.loopWith cm) improved

theorem frame
 (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum : base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyWith cm)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
 unfold bodyWith
 apply LocalEFoldBody.frame L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup c
  LowAccCarryDevelop.control_outside (LowAccCarryDevelop.loopWith cm) (LowAccCarryDevelop.loop_bstate_step cm)
  improved ?_ base M hM hP hc hsum O hO hg hSource
 intro b clean O0 E0 _ eb er off Q old
 exact LocalEFoldLift.transfer b clean O0 E0 eb er off Q old

#print axioms frame
end ECDSAAdd.Entrant.LocalEFoldBody90

end

section
-- Preserved checked proof component: LocalEFoldBody90Costs
namespace ECDSAAdd.Entrant.LocalEFoldBody90Costs
open ECDSAAdd Arithmetic Challenge ControlLoan1589BFFold LocalEFoldOptimize LocalEFoldAnchor LocalEFoldBody90
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] toffoliCount measurementCount gateSlots wires actual improved
abbrev CM := ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c)
def pre (cm : CM) : Program := measuredFoldQTq L (negP L)++
 (measuredFoldQTq L (rot128F L)++LowAccCarryDevelop.foldFor L (LowAccCarryDevelop.loopWith cm))
def post : Program := ParkCarry10Develop.rebuild L

theorem old_shape (cm : CM) : LowAccCarryDevelop.bodyWith cm=pre cm++(actual++post) := by
 simp only [LowAccCarryDevelop.bodyWith,LowAccCarryDevelop.foldWith,LowAccCarryDevelop.foldFor,
  pre,post,actual,List.append_assoc]
theorem new_shape (cm : CM) : bodyWith cm=pre cm++(improved++post) := by
 simp only [bodyWith,LocalEFoldBody.bodyForFold,LowAccCarryDevelop.foldFor,pre,post,List.append_assoc]

theorem toffoli (cm : CM) : toffoliCount (bodyWith cm)+2=toffoliCount (LowAccCarryDevelop.bodyWith cm) := by
 rw [old_shape,new_shape]
 simp only [toffoliCount_append]
 have h:=LocalEFoldResources.toffoli
 omega

theorem measurements (cm : CM) : measurementCount (bodyWith cm)=measurementCount (LowAccCarryDevelop.bodyWith cm) := by
 rw [old_shape,new_shape]
 simp only [measurementCount_append,LocalEFoldResources.measurements]

theorem slots (cm : CM) : gateSlots (bodyWith cm)=gateSlots (LowAccCarryDevelop.bodyWith cm) := by
 rw [old_shape,new_shape]
 simp only [gateSlots_append,LocalEFoldResources.slots]

theorem resources (cm : CM) :
 toffoliCount (bodyWith cm)+90≤toffoliCount (ParkCarry10Develop.body L c) ∧
 measurementCount (bodyWith cm)=measurementCount (ParkCarry10Develop.body L c) ∧
 gateSlots (bodyWith cm)+264≤gateSlots (ParkCarry10Develop.body L c) := by
 dsimp only [LocalEFoldBody90.L,LocalEFoldBody90.c]
 have old:=LowAccCarryDevelop.body_resources cm
 have t:=toffoli cm
 have m:=measurements cm
 have g:=slots cm
 exact ⟨by omega,m.trans old.2.1,by omega⟩

theorem support (cm : CM) : wires (bodyWith cm)⊆wires (LowAccCarryDevelop.bodyWith cm) := by
 rw [new_shape,old_shape,wires_append,wires_append,wires_append,wires_append]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union LocalEFoldResources.support (Finset.Subset.refl _))

theorem physical (cm : CM) : GatePhysical (bodyWith cm) := by
 have h:=LowAccCarryDevelop.body_physical cm
 rw [old_shape,gatePhysical_append,gatePhysical_append] at h
 rw [new_shape,gatePhysical_append,gatePhysical_append]
 exact ⟨h.1,LocalEFoldResources.physical h.2.1,h.2.2⟩
#print axioms resources
#print axioms physical
end ECDSAAdd.Entrant.LocalEFoldBody90Costs

end

section
-- Preserved checked proof component: LocalEFoldSelector90
namespace ECDSAAdd.Entrant.LocalEFoldBody90Costs
open ECDSAAdd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
theorem support_old (cm : CM) : wires (LocalEFoldBody90.bodyWith cm)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) :=
 (support cm).trans (LowAccCarryDevelop.body_support cm)
end ECDSAAdd.Entrant.LocalEFoldBody90Costs
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullB90FoldOptTemp
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.Arithmetic.GatePhysical
attribute [local irreducible] ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots ECDSAAdd.regValue
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem option_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hf : P fallback) (hb : ∀a,P (body a)) (result : Option α) : P (result.elim fallback body) := by
 cases result with
 | none => exact hf
 | some a => exact hb a

theorem option_some_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hb : ∀a,P (body a)) (result : Option α) (success : result.isSome=true) : P (result.elim fallback body) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at success
 | some a => exact hb a

theorem option_map_success {α β : Type} (result : Option α) (f : α → β) :
 (result.map f).isSome=result.isSome := by
 cases result <;> rfl

theorem actual_resources :
 toffoliCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith)+90≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith)=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith)+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_some_property (fun p=>
  toffoliCount p+90≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  measurementCount p=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  Challenge.gateSlots p+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith LocalEFoldBody90Costs.resources ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)
  ((option_map_success (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0) LowAccCarryDevelop.fromLiteral).trans LowAccCarryDevelop.success_literal)

theorem actual_subset : wires (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_property (fun p=>wires p⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith (Finset.Subset.refl (wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))) LocalEFoldBody90Costs.support_old ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_physical : GatePhysical (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith) := by
 exact option_property GatePhysical (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith
  (ParkCarry10Develop.body_physical LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.c LowAccCarryDevelop.layout_control_nodup)
  LocalEFoldBody90Costs.physical ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith)
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) := by
 exact option_property (fun p=>Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) p
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O))) (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith
  (ParkCarry10Develop.body_frame LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.layout_nodup LowAccCarryDevelop.c LowAccCarryDevelop.control_outside
   base M hM hP hc hsum O hO hg hSource)
  (fun cm=>LocalEFoldBody90.frame cm base M hM hP hc hsum O hO hg hSource) ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => ParkCarry10Develop.body K g
 | isTrue _ => if g=LowAccCarryDevelop.c then (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith) else ParkCarry10Develop.body K g

theorem selected_body_transport (K K' : CuccaroStreamedSquareWideLayout) (g g' : Wire)
 (he : K=K') (hg : g=g') : selectedBody K g=selectedBody K' g' := by
 cases he
 cases hg
 rfl

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 wires (selectedBody K g)⊆wires (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact Finset.Subset.refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_subset
  · exact Finset.Subset.refl _

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c)⊆(c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths)
 (g : Wire) (nd : (g::K.wires).Nodup) : GatePhysical (selectedBody K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ParkCarry10Develop.body_physical K hw g nd
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_physical
  · exact ParkCarry10Develop.body_physical K hw g nd

theorem selected_frame (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (hn : K.wires.Nodup)
 (g : Wire) (hcw : g∉K.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue K.core.product base=M^2) (hc : K.PairClean base)
 (hsum : base K.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base g=false → M=0) (hSource : M=if base g then regValue K.core.high base else 0) :
 Triple (SquareFrame K.core.out base O) (selectedBody K g)
  (SquareFrame K.core.out base (bO4 (M^2) (base g) O)) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hne => exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource
 | isTrue hl =>
  dsimp only
  split
  · rename_i hgc;subst K;subst g;exact actual_frame base M hM hP hc hsum O hO hg hSource
  · exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource

theorem selected_resources (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 toffoliCount (selectedBody K g)≤toffoliCount (ParkCarry10Develop.body K g) ∧
 measurementCount (selectedBody K g)=measurementCount (ParkCarry10Develop.body K g) ∧
 Challenge.gateSlots (selectedBody K g)≤Challenge.gateSlots (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g
    have h:=actual_resources
    exact ⟨by omega,h.2.1,by omega⟩
  · exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c=selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c)≤toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c)≤Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 selected_resources (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c)⊆wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

abbrev actualLayout := FullBOptTemp.actualLayout
abbrev actualControl := FullBOptTemp.actualControl
abbrev actualExt := FullBOptTemp.actualExt
abbrev actualFoldPerm := FullBOptTemp.actualFoldPerm

theorem selected_actual : selectedBody LowAccCarryDevelop.L LowAccCarryDevelop.c=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq LowAccCarryDevelop.L LowAccCarryDevelop.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

theorem ranked_selected_exact : hostedSelectedBody actualLayout actualFoldPerm actualControl=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalEFoldBody90.bodyWith) := by
 have he : ParkCarryDevelop.hostLayout actualLayout actualFoldPerm=actualLayout :=
  FullBOptTemp.actualHostedLayout_eq
 exact (congrArg (fun K=>selectedBody K actualControl) he).trans
  ((selected_body_transport actualLayout LowAccCarryDevelop.L actualControl LowAccCarryDevelop.c rfl rfl).trans selected_actual)

theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+90≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 := by
 rw [ranked_selected_exact]
 have h:=actual_resources
 have old:=ParkCarry10Develop.body_counts LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.c
 exact ⟨h.1.trans old.1.le,h.2.1.trans old.2⟩

end ECDSAAdd.Entrant.FullB90FoldOptTemp
#print axioms ECDSAAdd.Entrant.FullB90FoldOptTemp.actual_frame
#print axioms ECDSAAdd.Entrant.FullB90FoldOptTemp.ranked_certified_gain

end

section
-- Preserved checked rebuild component: LocalRebuild
namespace ECDSAAdd.Entrant.LocalRebuild
open ECDSAAdd Arithmetic SixCarryTrace SixCarryFrame SixCarryReplacement
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
def chunk0 : Program := [
.CX 4243 4115,
.CX 4243 4760,
.CCX 4115 4760 4373,
.CX 4243 4373,
.CX 4243 4760,
.CX 4243 4115,
.CX 4244 4116,
.CX 4244 4373,
.CCX 4116 4373 4374,
.CX 4244 4374,
.CX 4244 4373,
.CX 4244 4116,
.CX 4245 4117,
.CX 4245 4374,
.CCX 4117 4374 4375,
.CX 4245 4375,
.CX 4245 4374,
.CX 4245 4117,
.CX 4246 4118,
.CX 4246 4375,
.CCX 4118 4375 4376,
.CX 4246 4376,
.CX 4246 4375,
.CX 4246 4118,
.CX 4247 4119,
.CX 4247 4376,
.CCX 4119 4376 4377,
.CX 4247 4377,
.CX 4247 4376,
.CX 4247 4119,
.CX 4248 4120,
.CX 4248 4377,
.CCX 4120 4377 4378,
.CX 4248 4378,
.CX 4248 4377,
.CX 4248 4120,
.CX 4249 4121,
.CX 4249 4378,
.CCX 4121 4378 4379,
.CX 4249 4379,
.CX 4249 4378,
.CX 4249 4121,
.CX 4250 4122,
.CX 4250 4379,
.CCX 4122 4379 4380,
.CX 4250 4380,
.CX 4250 4379,
.CX 4250 4122,
.CX 4251 4123,
.CX 4251 4380,
.CCX 4123 4380 4381,
.CX 4251 4381,
.CX 4251 4380,
.CX 4251 4123,
.CX 4252 4124,
.CX 4252 4381,
.CCX 4124 4381 4382,
.CX 4252 4382,
.CX 4252 4381,
.CX 4252 4124,
.CX 4253 4125,
.CX 4253 4382,
.CCX 4125 4382 4383,
.CX 4253 4383,
.CX 4253 4382,
.CX 4253 4125,
.CX 4254 4126,
.CX 4254 4383,
.CCX 4126 4383 4384,
.CX 4254 4384,
.CX 4254 4383,
.CX 4254 4126,
.CX 4255 4127,
.CX 4255 4384,
.CCX 4127 4384 4385,
.CX 4255 4385,
.CX 4255 4384,
.CX 4255 4127,
.CX 4256 4128,
.CX 4256 4385,
.CCX 4128 4385 4386,
.CX 4256 4386,
.CX 4256 4385,
.CX 4256 4128,
.CX 4257 4129,
.CX 4257 4386,
.CCX 4129 4386 4387,
.CX 4257 4387,
.CX 4257 4386,
.CX 4257 4129,
.CX 4258 4130,
.CX 4258 4387,
.CCX 4130 4387 4388,
.CX 4258 4388,
.CX 4258 4387,
.CX 4258 4130,
.CX 4259 4131,
.CX 4259 4388,
.CCX 4131 4388 4389,
.CX 4259 4389,
.CX 4259 4388,
.CX 4259 4131,
.CX 4260 4132,
.CX 4260 4389,
.CCX 4132 4389 4390,
.CX 4260 4390,
.CX 4260 4389,
.CX 4260 4132,
.CX 4261 4133,
.CX 4261 4390,
.CCX 4133 4390 4391,
.CX 4261 4391,
.CX 4261 4390,
.CX 4261 4133,
.CX 4262 4134,
.CX 4262 4391,
.CCX 4134 4391 4392,
.CX 4262 4392,
.CX 4262 4391,
.CX 4262 4134,
.CX 4263 4135,
.CX 4263 4392,
.CCX 4135 4392 4393,
.CX 4263 4393,
.CX 4263 4392,
.CX 4263 4135,
.CX 4264 4136,
.CX 4264 4393
]
def chunk1 : Program := [
.CCX 4136 4393 4394,
.CX 4264 4394,
.CX 4264 4393,
.CX 4264 4136,
.CX 4265 4137,
.CX 4265 4394,
.CCX 4137 4394 4395,
.CX 4265 4395,
.CX 4265 4394,
.CX 4265 4137,
.CX 4266 4138,
.CX 4266 4395,
.CCX 4138 4395 4396,
.CX 4266 4396,
.CX 4266 4395,
.CX 4266 4138,
.CX 4267 4139,
.CX 4267 4396,
.CCX 4139 4396 4397,
.CX 4267 4397,
.CX 4267 4396,
.CX 4267 4139,
.CX 4268 4140,
.CX 4268 4397,
.CCX 4140 4397 4398,
.CX 4268 4398,
.CX 4268 4397,
.CX 4268 4140,
.CX 4269 4141,
.CX 4269 4398,
.CCX 4141 4398 4399,
.CX 4269 4399,
.CX 4269 4398,
.CX 4269 4141,
.CX 4270 4142,
.CX 4270 4399,
.CCX 4142 4399 4400,
.CX 4270 4400,
.CX 4270 4399,
.CX 4270 4142,
.CX 4271 4143,
.CX 4271 4400,
.CCX 4143 4400 4401,
.CX 4271 4401,
.CX 4271 4400,
.CX 4271 4143,
.CX 4272 4144,
.CX 4272 4401,
.CCX 4144 4401 4402,
.CX 4272 4402,
.CX 4272 4401,
.CX 4272 4144,
.CX 4273 4145,
.CX 4273 4402,
.CCX 4145 4402 4403,
.CX 4273 4403,
.CX 4273 4402,
.CX 4273 4145,
.CX 4274 4146,
.CX 4274 4403,
.CCX 4146 4403 4404,
.CX 4274 4404,
.CX 4274 4403,
.CX 4274 4146,
.CX 4275 4147,
.CX 4275 4404,
.CCX 4147 4404 4405,
.CX 4275 4405,
.CX 4275 4404,
.CX 4275 4147,
.CX 4276 4148,
.CX 4276 4405,
.CCX 4148 4405 4406,
.CX 4276 4406,
.CX 4276 4405,
.CX 4276 4148,
.CX 4277 4149,
.CX 4277 4406,
.CCX 4149 4406 4407,
.CX 4277 4407,
.CX 4277 4406,
.CX 4277 4149,
.CX 4278 4150,
.CX 4278 4407,
.CCX 4150 4407 4408,
.CX 4278 4408,
.CX 4278 4407,
.CX 4278 4150,
.CX 4279 4151,
.CX 4279 4408,
.CCX 4151 4408 4409,
.CX 4279 4409,
.CX 4279 4408,
.CX 4279 4151,
.CX 4280 4152,
.CX 4280 4409,
.CCX 4152 4409 4410,
.CX 4280 4410,
.CX 4280 4409,
.CX 4280 4152,
.CX 4281 4153,
.CX 4281 4410,
.CCX 4153 4410 4411,
.CX 4281 4411,
.CX 4281 4410,
.CX 4281 4153,
.CX 4282 4154,
.CX 4282 4411,
.CCX 4154 4411 4412,
.CX 4282 4412,
.CX 4282 4411,
.CX 4282 4154,
.CX 4283 4155,
.CX 4283 4412,
.CCX 4155 4412 4413,
.CX 4283 4413,
.CX 4283 4412,
.CX 4283 4155,
.CX 4284 4156,
.CX 4284 4413,
.CCX 4156 4413 4414,
.CX 4284 4414,
.CX 4284 4413,
.CX 4284 4156,
.CX 4285 4157,
.CX 4285 4414,
.CCX 4157 4414 4415,
.CX 4285 4415
]
def chunk2 : Program := [
.CX 4285 4414,
.CX 4285 4157,
.CX 4286 4158,
.CX 4286 4415,
.CCX 4158 4415 4416,
.CX 4286 4416,
.CX 4286 4415,
.CX 4286 4158,
.CX 4287 4159,
.CX 4287 4416,
.CCX 4159 4416 4417,
.CX 4287 4417,
.CX 4287 4416,
.CX 4287 4159,
.CX 4288 4160,
.CX 4288 4417,
.CCX 4160 4417 4418,
.CX 4288 4418,
.CX 4288 4417,
.CX 4288 4160,
.CX 4289 4161,
.CX 4289 4418,
.CCX 4161 4418 4419,
.CX 4289 4419,
.CX 4289 4418,
.CX 4289 4161,
.CX 4290 4162,
.CX 4290 4419,
.CCX 4162 4419 4420,
.CX 4290 4420,
.CX 4290 4419,
.CX 4290 4162,
.CX 4291 4163,
.CX 4291 4420,
.CCX 4163 4420 4421,
.CX 4291 4421,
.CX 4291 4420,
.CX 4291 4163,
.CX 4292 4164,
.CX 4292 4421,
.CCX 4164 4421 4422,
.CX 4292 4422,
.CX 4292 4421,
.CX 4292 4164,
.CX 4293 4165,
.CX 4293 4422,
.CCX 4165 4422 4423,
.CX 4293 4423,
.CX 4293 4422,
.CX 4293 4165,
.CX 4294 4166,
.CX 4294 4423,
.CCX 4166 4423 4424,
.CX 4294 4424,
.CX 4294 4423,
.CX 4294 4166,
.CX 4295 4167,
.CX 4295 4424,
.CCX 4167 4424 4425,
.CX 4295 4425,
.CX 4295 4424,
.CX 4295 4167,
.CX 4296 4168,
.CX 4296 4425,
.CCX 4168 4425 4426,
.CX 4296 4426,
.CX 4296 4425,
.CX 4296 4168,
.CX 4297 4169,
.CX 4297 4426,
.CCX 4169 4426 4427,
.CX 4297 4427,
.CX 4297 4426,
.CX 4297 4169,
.CX 4298 4170,
.CX 4298 4427,
.CCX 4170 4427 4428,
.CX 4298 4428,
.CX 4298 4427,
.CX 4298 4170,
.CX 4299 4171,
.CX 4299 4428,
.CCX 4171 4428 4429,
.CX 4299 4429,
.CX 4299 4428,
.CX 4299 4171,
.CX 4300 4172,
.CX 4300 4429,
.CCX 4172 4429 4430,
.CX 4300 4430,
.CX 4300 4429,
.CX 4300 4172,
.CX 4301 4173,
.CX 4301 4430,
.CCX 4173 4430 4431,
.CX 4301 4431,
.CX 4301 4430,
.CX 4301 4173,
.CX 4302 4174,
.CX 4302 4431,
.CCX 4174 4431 4432,
.CX 4302 4432,
.CX 4302 4431,
.CX 4302 4174,
.CX 4303 4175,
.CX 4303 4432,
.CCX 4175 4432 4433,
.CX 4303 4433,
.CX 4303 4432,
.CX 4303 4175,
.CX 4304 4176,
.CX 4304 4433,
.CCX 4176 4433 4434,
.CX 4304 4434,
.CX 4304 4433,
.CX 4304 4176,
.CX 4305 4177,
.CX 4305 4434,
.CCX 4177 4434 4435,
.CX 4305 4435,
.CX 4305 4434,
.CX 4305 4177,
.CX 4306 4178,
.CX 4306 4435,
.CCX 4178 4435 4436,
.CX 4306 4436,
.CX 4306 4435,
.CX 4306 4178
]
def chunk3 : Program := [
.CX 4307 4179,
.CX 4307 4436,
.CCX 4179 4436 4437,
.CX 4307 4437,
.CX 4307 4436,
.CX 4307 4179,
.CX 4308 4180,
.CX 4308 4437,
.CCX 4180 4437 4438,
.CX 4308 4438,
.CX 4308 4437,
.CX 4308 4180,
.CX 4309 4181,
.CX 4309 4438,
.CCX 4181 4438 4439,
.CX 4309 4439,
.CX 4309 4438,
.CX 4309 4181,
.CX 4310 4182,
.CX 4310 4439,
.CCX 4182 4439 4440,
.CX 4310 4440,
.CX 4310 4439,
.CX 4310 4182,
.CX 4311 4183,
.CX 4311 4440,
.CCX 4183 4440 4441,
.CX 4311 4441,
.CX 4311 4440,
.CX 4311 4183,
.CX 4312 4184,
.CX 4312 4441,
.CCX 4184 4441 4442,
.CX 4312 4442,
.CX 4312 4441,
.CX 4312 4184,
.CX 4313 4185,
.CX 4313 4442,
.CCX 4185 4442 4443,
.CX 4313 4443,
.CX 4313 4442,
.CX 4313 4185,
.CX 4314 4186,
.CX 4314 4443,
.CCX 4186 4443 4444,
.CX 4314 4444,
.CX 4314 4443,
.CX 4314 4186,
.CX 4315 4187,
.CX 4315 4444,
.CCX 4187 4444 4445,
.CX 4315 4445,
.CX 4315 4444,
.CX 4315 4187,
.CX 4316 4188,
.CX 4316 4445,
.CCX 4188 4445 4446,
.CX 4316 4446,
.CX 4316 4445,
.CX 4316 4188,
.CX 4317 4189,
.CX 4317 4446,
.CCX 4189 4446 4447,
.CX 4317 4447,
.CX 4317 4446,
.CX 4317 4189,
.CX 4318 4190,
.CX 4318 4447,
.CCX 4190 4447 4448,
.CX 4318 4448,
.CX 4318 4447,
.CX 4318 4190,
.CX 4319 4191,
.CX 4319 4448,
.CCX 4191 4448 4449,
.CX 4319 4449,
.CX 4319 4448,
.CX 4319 4191,
.CX 4320 4192,
.CX 4320 4449,
.CCX 4192 4449 4450,
.CX 4320 4450,
.CX 4320 4449,
.CX 4320 4192,
.CX 4321 4193,
.CX 4321 4450,
.CCX 4193 4450 4451,
.CX 4321 4451,
.CX 4321 4450,
.CX 4321 4193,
.CX 4322 4194,
.CX 4322 4451,
.CCX 4194 4451 4452,
.CX 4322 4452,
.CX 4322 4451,
.CX 4322 4194,
.CX 4323 4195,
.CX 4323 4452,
.CCX 4195 4452 4453,
.CX 4323 4453,
.CX 4323 4452,
.CX 4323 4195,
.CX 4324 4196,
.CX 4324 4453,
.CCX 4196 4453 4454,
.CX 4324 4454,
.CX 4324 4453,
.CX 4324 4196,
.CX 4325 4197,
.CX 4325 4454,
.CCX 4197 4454 4455,
.CX 4325 4455,
.CX 4325 4454,
.CX 4325 4197,
.CX 4326 4198,
.CX 4326 4455,
.CCX 4198 4455 4456,
.CX 4326 4456,
.CX 4326 4455,
.CX 4326 4198,
.CX 4327 4199,
.CX 4327 4456,
.CCX 4199 4456 4457,
.CX 4327 4457,
.CX 4327 4456,
.CX 4327 4199,
.CX 4328 4200,
.CX 4328 4457
]
def chunk4 : Program := [
.CCX 4200 4457 4458,
.CX 4328 4458,
.CX 4328 4457,
.CX 4328 4200,
.CX 4329 4201,
.CX 4329 4458,
.CCX 4201 4458 4459,
.CX 4329 4459,
.CX 4329 4458,
.CX 4329 4201,
.CX 4330 4202,
.CX 4330 4459,
.CCX 4202 4459 4460,
.CX 4330 4460,
.CX 4330 4459,
.CX 4330 4202,
.CX 4331 4203,
.CX 4331 4460,
.CCX 4203 4460 4461,
.CX 4331 4461,
.CX 4331 4460,
.CX 4331 4203,
.CX 4332 4204,
.CX 4332 4461,
.CCX 4204 4461 4462,
.CX 4332 4462,
.CX 4332 4461,
.CX 4332 4204,
.CX 4333 4205,
.CX 4333 4462,
.CCX 4205 4462 4463,
.CX 4333 4463,
.CX 4333 4462,
.CX 4333 4205,
.CX 4334 4206,
.CX 4334 4463,
.CCX 4206 4463 4464,
.CX 4334 4464,
.CX 4334 4463,
.CX 4334 4206,
.CX 4335 4207,
.CX 4335 4464,
.CCX 4207 4464 4465,
.CX 4335 4465,
.CX 4335 4464,
.CX 4335 4207,
.CX 4336 4208,
.CX 4336 4465,
.CCX 4208 4465 4466,
.CX 4336 4466,
.CX 4336 4465,
.CX 4336 4208,
.CX 4337 4209,
.CX 4337 4466,
.CCX 4209 4466 4467,
.CX 4337 4467,
.CX 4337 4466,
.CX 4337 4209,
.CX 4338 4210,
.CX 4338 4467,
.CCX 4210 4467 4468,
.CX 4338 4468,
.CX 4338 4467,
.CX 4338 4210,
.CX 4339 4211,
.CX 4339 4468,
.CCX 4211 4468 4469,
.CX 4339 4469,
.CX 4339 4468,
.CX 4339 4211,
.CX 4340 4212,
.CX 4340 4469,
.CCX 4212 4469 4470,
.CX 4340 4470,
.CX 4340 4469,
.CX 4340 4212,
.CX 4341 4213,
.CX 4341 4470,
.CCX 4213 4470 4471,
.CX 4341 4471,
.CX 4341 4470,
.CX 4341 4213,
.CX 4342 4214,
.CX 4342 4471,
.CCX 4214 4471 4472,
.CX 4342 4472,
.CX 4342 4471,
.CX 4342 4214,
.CX 4343 4215,
.CX 4343 4472,
.CCX 4215 4472 4473,
.CX 4343 4473,
.CX 4343 4472,
.CX 4343 4215,
.CX 4344 4216,
.CX 4344 4473,
.CCX 4216 4473 4474,
.CX 4344 4474,
.CX 4344 4473,
.CX 4344 4216,
.CX 4345 4217,
.CX 4345 4474,
.CCX 4217 4474 4475,
.CX 4345 4475,
.CX 4345 4474,
.CX 4345 4217,
.CX 4346 4218,
.CX 4346 4475,
.CCX 4218 4475 4476,
.CX 4346 4476,
.CX 4346 4475,
.CX 4346 4218,
.CX 4347 4219,
.CX 4347 4476,
.CCX 4219 4476 4477,
.CX 4347 4477,
.CX 4347 4476,
.CX 4347 4219,
.CX 4348 4220,
.CX 4348 4477,
.CCX 4220 4477 4478,
.CX 4348 4478,
.CX 4348 4477,
.CX 4348 4220,
.CX 4349 4221,
.CX 4349 4478,
.CCX 4221 4478 4479,
.CX 4349 4479
]
def chunk5 : Program := [
.CX 4349 4478,
.CX 4349 4221,
.CX 4350 4222,
.CX 4350 4479,
.CCX 4222 4479 4480,
.CX 4350 4480,
.CX 4350 4479,
.CX 4350 4222,
.CX 4351 4223,
.CX 4351 4480,
.CCX 4223 4480 4481,
.CX 4351 4481,
.CX 4351 4480,
.CX 4351 4223,
.CX 4352 4224,
.CX 4352 4481,
.CCX 4224 4481 4482,
.CX 4352 4482,
.CX 4352 4481,
.CX 4352 4224,
.CX 4353 4225,
.CX 4353 4482,
.CCX 4225 4482 4483,
.CX 4353 4483,
.CX 4353 4482,
.CX 4353 4225,
.CX 4354 4226,
.CX 4354 4483,
.CCX 4226 4483 4484,
.CX 4354 4484,
.CX 4354 4483,
.CX 4354 4226,
.CX 4355 4227,
.CX 4355 4484,
.CCX 4227 4484 4485,
.CX 4355 4485,
.CX 4355 4484,
.CX 4355 4227,
.CX 4356 4228,
.CX 4356 4485,
.CCX 4228 4485 4486,
.CX 4356 4486,
.CX 4356 4485,
.CX 4356 4228,
.CX 4357 4229,
.CX 4357 4486,
.CCX 4229 4486 4487,
.CX 4357 4487,
.CX 4357 4486,
.CX 4357 4229,
.CX 4358 4230,
.CX 4358 4487,
.CCX 4230 4487 4488,
.CX 4358 4488,
.CX 4358 4487,
.CX 4358 4230,
.CX 4359 4231,
.CX 4359 4488,
.CCX 4231 4488 4489,
.CX 4359 4489,
.CX 4359 4488,
.CX 4359 4231,
.CX 4360 4232,
.CX 4360 4489,
.CCX 4232 4489 4490,
.CX 4360 4490,
.CX 4360 4489,
.CX 4360 4232,
.CX 4361 4233,
.CX 4361 4490,
.CCX 4233 4490 4491,
.CX 4361 4491,
.CX 4361 4490,
.CX 4361 4233,
.CX 4362 4234,
.CX 4362 4491,
.CCX 4234 4491 4492,
.CX 4362 4492,
.CX 4362 4491,
.CX 4362 4234,
.CX 4363 4235,
.CX 4363 4492,
.CCX 4235 4492 4493,
.CX 4363 4493,
.CX 4363 4492,
.CX 4363 4235,
.CX 4364 4236,
.CX 4364 4493,
.CCX 4236 4493 4494,
.CX 4364 4494,
.CX 4364 4493,
.CX 4364 4236,
.CX 4365 4237,
.CX 4365 4494,
.CCX 4237 4494 4495,
.CX 4365 4495,
.CX 4365 4494,
.CX 4365 4237,
.CX 4366 4238,
.CX 4366 4495,
.CCX 4238 4495 4496,
.CX 4366 4496,
.CX 4366 4495,
.CX 4366 4238,
.CX 4367 4239,
.CX 4367 4496,
.CCX 4239 4496 4497,
.CX 4367 4497,
.CX 4367 4496,
.CX 4367 4239,
.CX 4368 4240,
.CX 4368 4497,
.CCX 4240 4497 4498,
.CX 4368 4498,
.CX 4368 4497,
.CX 4368 4240,
.CX 4369 4241,
.CX 4369 4498,
.CCX 4241 4498 4499,
.CX 4369 4499,
.CX 4369 4498,
.CX 4369 4241,
.CX 4370 4242,
.CX 4370 4499,
.CCX 4242 4499 4500,
.CX 4370 4500,
.CX 4370 4499,
.CX 4370 4242
]
def chunk6 : Program := [
.measureX 4372 [] [.CZ 4765 4371,.CZ 4765 4500,.CZ 4371 4500],
.CX 4765 4371,
.CX 4500 4371,
.measureX 4500 [] [.CZ 4370 4242,.CZ 4370 4499,.CZ 4242 4499],
.CX 4370 4242,
.CX 4499 4242,
.measureX 4499 [] [.CZ 4369 4241,.CZ 4369 4498,.CZ 4241 4498],
.CX 4369 4241,
.CX 4498 4241,
.measureX 4498 [] [.CZ 4368 4240,.CZ 4368 4497,.CZ 4240 4497],
.CX 4368 4240,
.CX 4497 4240,
.measureX 4497 [] [.CZ 4367 4239,.CZ 4367 4496,.CZ 4239 4496],
.CX 4367 4239,
.CX 4496 4239,
.measureX 4496 [] [.CZ 4366 4238,.CZ 4366 4495,.CZ 4238 4495],
.CX 4366 4238,
.CX 4495 4238,
.measureX 4495 [] [.CZ 4365 4237,.CZ 4365 4494,.CZ 4237 4494],
.CX 4365 4237,
.CX 4494 4237,
.measureX 4494 [] [.CZ 4364 4236,.CZ 4364 4493,.CZ 4236 4493],
.CX 4364 4236,
.CX 4493 4236,
.measureX 4493 [] [.CZ 4363 4235,.CZ 4363 4492,.CZ 4235 4492],
.CX 4363 4235,
.CX 4492 4235,
.measureX 4492 [] [.CZ 4362 4234,.CZ 4362 4491,.CZ 4234 4491],
.CX 4362 4234,
.CX 4491 4234,
.measureX 4491 [] [.CZ 4361 4233,.CZ 4361 4490,.CZ 4233 4490],
.CX 4361 4233,
.CX 4490 4233,
.measureX 4490 [] [.CZ 4360 4232,.CZ 4360 4489,.CZ 4232 4489],
.CX 4360 4232,
.CX 4489 4232,
.measureX 4489 [] [.CZ 4359 4231,.CZ 4359 4488,.CZ 4231 4488],
.CX 4359 4231,
.CX 4488 4231,
.measureX 4488 [] [.CZ 4358 4230,.CZ 4358 4487,.CZ 4230 4487],
.CX 4358 4230,
.CX 4487 4230,
.measureX 4487 [] [.CZ 4357 4229,.CZ 4357 4486,.CZ 4229 4486],
.CX 4357 4229,
.CX 4486 4229,
.measureX 4486 [] [.CZ 4356 4228,.CZ 4356 4485,.CZ 4228 4485],
.CX 4356 4228,
.CX 4485 4228,
.measureX 4485 [] [.CZ 4355 4227,.CZ 4355 4484,.CZ 4227 4484],
.CX 4355 4227,
.CX 4484 4227,
.measureX 4484 [] [.CZ 4354 4226,.CZ 4354 4483,.CZ 4226 4483],
.CX 4354 4226,
.CX 4483 4226,
.measureX 4483 [] [.CZ 4353 4225,.CZ 4353 4482,.CZ 4225 4482],
.CX 4353 4225,
.CX 4482 4225,
.measureX 4482 [] [.CZ 4352 4224,.CZ 4352 4481,.CZ 4224 4481],
.CX 4352 4224,
.CX 4481 4224,
.measureX 4481 [] [.CZ 4351 4223,.CZ 4351 4480,.CZ 4223 4480],
.CX 4351 4223,
.CX 4480 4223,
.measureX 4480 [] [.CZ 4350 4222,.CZ 4350 4479,.CZ 4222 4479],
.CX 4350 4222,
.CX 4479 4222,
.measureX 4479 [] [.CZ 4349 4221,.CZ 4349 4478,.CZ 4221 4478],
.CX 4349 4221,
.CX 4478 4221,
.measureX 4478 [] [.CZ 4348 4220,.CZ 4348 4477,.CZ 4220 4477],
.CX 4348 4220,
.CX 4477 4220,
.measureX 4477 [] [.CZ 4347 4219,.CZ 4347 4476,.CZ 4219 4476],
.CX 4347 4219,
.CX 4476 4219,
.measureX 4476 [] [.CZ 4346 4218,.CZ 4346 4475,.CZ 4218 4475],
.CX 4346 4218,
.CX 4475 4218,
.measureX 4475 [] [.CZ 4345 4217,.CZ 4345 4474,.CZ 4217 4474],
.CX 4345 4217,
.CX 4474 4217,
.measureX 4474 [] [.CZ 4344 4216,.CZ 4344 4473,.CZ 4216 4473],
.CX 4344 4216,
.CX 4473 4216,
.measureX 4473 [] [.CZ 4343 4215,.CZ 4343 4472,.CZ 4215 4472],
.CX 4343 4215,
.CX 4472 4215,
.measureX 4472 [] [.CZ 4342 4214,.CZ 4342 4471,.CZ 4214 4471],
.CX 4342 4214,
.CX 4471 4214,
.measureX 4471 [] [.CZ 4341 4213,.CZ 4341 4470,.CZ 4213 4470],
.CX 4341 4213,
.CX 4470 4213,
.measureX 4470 [] [.CZ 4340 4212,.CZ 4340 4469,.CZ 4212 4469],
.CX 4340 4212,
.CX 4469 4212,
.measureX 4469 [] [.CZ 4339 4211,.CZ 4339 4468,.CZ 4211 4468],
.CX 4339 4211,
.CX 4468 4211,
.measureX 4468 [] [.CZ 4338 4210,.CZ 4338 4467,.CZ 4210 4467],
.CX 4338 4210,
.CX 4467 4210,
.measureX 4467 [] [.CZ 4337 4209,.CZ 4337 4466,.CZ 4209 4466],
.CX 4337 4209,
.CX 4466 4209,
.measureX 4466 [] [.CZ 4336 4208,.CZ 4336 4465,.CZ 4208 4465],
.CX 4336 4208,
.CX 4465 4208,
.measureX 4465 [] [.CZ 4335 4207,.CZ 4335 4464,.CZ 4207 4464],
.CX 4335 4207,
.CX 4464 4207,
.measureX 4464 [] [.CZ 4334 4206,.CZ 4334 4463,.CZ 4206 4463],
.CX 4334 4206,
.CX 4463 4206,
.measureX 4463 [] [.CZ 4333 4205,.CZ 4333 4462,.CZ 4205 4462],
.CX 4333 4205,
.CX 4462 4205,
.measureX 4462 [] [.CZ 4332 4204,.CZ 4332 4461,.CZ 4204 4461],
.CX 4332 4204,
.CX 4461 4204,
.measureX 4461 [] [.CZ 4331 4203,.CZ 4331 4460,.CZ 4203 4460],
.CX 4331 4203,
.CX 4460 4203,
.measureX 4460 [] [.CZ 4330 4202,.CZ 4330 4459,.CZ 4202 4459],
.CX 4330 4202,
.CX 4459 4202,
.measureX 4459 [] [.CZ 4329 4201,.CZ 4329 4458,.CZ 4201 4458],
.CX 4329 4201
]
def chunk7 : Program := [
.CX 4458 4201,
.measureX 4458 [] [.CZ 4328 4200,.CZ 4328 4457,.CZ 4200 4457],
.CX 4328 4200,
.CX 4457 4200,
.measureX 4457 [] [.CZ 4327 4199,.CZ 4327 4456,.CZ 4199 4456],
.CX 4327 4199,
.CX 4456 4199,
.measureX 4456 [] [.CZ 4326 4198,.CZ 4326 4455,.CZ 4198 4455],
.CX 4326 4198,
.CX 4455 4198,
.measureX 4455 [] [.CZ 4325 4197,.CZ 4325 4454,.CZ 4197 4454],
.CX 4325 4197,
.CX 4454 4197,
.measureX 4454 [] [.CZ 4324 4196,.CZ 4324 4453,.CZ 4196 4453],
.CX 4324 4196,
.CX 4453 4196,
.measureX 4453 [] [.CZ 4323 4195,.CZ 4323 4452,.CZ 4195 4452],
.CX 4323 4195,
.CX 4452 4195,
.measureX 4452 [] [.CZ 4322 4194,.CZ 4322 4451,.CZ 4194 4451],
.CX 4322 4194,
.CX 4451 4194,
.measureX 4451 [] [.CZ 4321 4193,.CZ 4321 4450,.CZ 4193 4450],
.CX 4321 4193,
.CX 4450 4193,
.measureX 4450 [] [.CZ 4320 4192,.CZ 4320 4449,.CZ 4192 4449],
.CX 4320 4192,
.CX 4449 4192,
.measureX 4449 [] [.CZ 4319 4191,.CZ 4319 4448,.CZ 4191 4448],
.CX 4319 4191,
.CX 4448 4191,
.measureX 4448 [] [.CZ 4318 4190,.CZ 4318 4447,.CZ 4190 4447],
.CX 4318 4190,
.CX 4447 4190,
.measureX 4447 [] [.CZ 4317 4189,.CZ 4317 4446,.CZ 4189 4446],
.CX 4317 4189,
.CX 4446 4189,
.measureX 4446 [] [.CZ 4316 4188,.CZ 4316 4445,.CZ 4188 4445],
.CX 4316 4188,
.CX 4445 4188,
.measureX 4445 [] [.CZ 4315 4187,.CZ 4315 4444,.CZ 4187 4444],
.CX 4315 4187,
.CX 4444 4187,
.measureX 4444 [] [.CZ 4314 4186,.CZ 4314 4443,.CZ 4186 4443],
.CX 4314 4186,
.CX 4443 4186,
.measureX 4443 [] [.CZ 4313 4185,.CZ 4313 4442,.CZ 4185 4442],
.CX 4313 4185,
.CX 4442 4185,
.measureX 4442 [] [.CZ 4312 4184,.CZ 4312 4441,.CZ 4184 4441],
.CX 4312 4184,
.CX 4441 4184,
.measureX 4441 [] [.CZ 4311 4183,.CZ 4311 4440,.CZ 4183 4440],
.CX 4311 4183,
.CX 4440 4183,
.measureX 4440 [] [.CZ 4310 4182,.CZ 4310 4439,.CZ 4182 4439],
.CX 4310 4182,
.CX 4439 4182,
.measureX 4439 [] [.CZ 4309 4181,.CZ 4309 4438,.CZ 4181 4438],
.CX 4309 4181,
.CX 4438 4181,
.measureX 4438 [] [.CZ 4308 4180,.CZ 4308 4437,.CZ 4180 4437],
.CX 4308 4180,
.CX 4437 4180,
.measureX 4437 [] [.CZ 4307 4179,.CZ 4307 4436,.CZ 4179 4436],
.CX 4307 4179,
.CX 4436 4179,
.measureX 4436 [] [.CZ 4306 4178,.CZ 4306 4435,.CZ 4178 4435],
.CX 4306 4178,
.CX 4435 4178,
.measureX 4435 [] [.CZ 4305 4177,.CZ 4305 4434,.CZ 4177 4434],
.CX 4305 4177,
.CX 4434 4177,
.measureX 4434 [] [.CZ 4304 4176,.CZ 4304 4433,.CZ 4176 4433],
.CX 4304 4176,
.CX 4433 4176,
.measureX 4433 [] [.CZ 4303 4175,.CZ 4303 4432,.CZ 4175 4432],
.CX 4303 4175,
.CX 4432 4175,
.measureX 4432 [] [.CZ 4302 4174,.CZ 4302 4431,.CZ 4174 4431],
.CX 4302 4174,
.CX 4431 4174,
.measureX 4431 [] [.CZ 4301 4173,.CZ 4301 4430,.CZ 4173 4430],
.CX 4301 4173,
.CX 4430 4173,
.measureX 4430 [] [.CZ 4300 4172,.CZ 4300 4429,.CZ 4172 4429],
.CX 4300 4172,
.CX 4429 4172,
.measureX 4429 [] [.CZ 4299 4171,.CZ 4299 4428,.CZ 4171 4428],
.CX 4299 4171,
.CX 4428 4171,
.measureX 4428 [] [.CZ 4298 4170,.CZ 4298 4427,.CZ 4170 4427],
.CX 4298 4170,
.CX 4427 4170,
.measureX 4427 [] [.CZ 4297 4169,.CZ 4297 4426,.CZ 4169 4426],
.CX 4297 4169,
.CX 4426 4169,
.measureX 4426 [] [.CZ 4296 4168,.CZ 4296 4425,.CZ 4168 4425],
.CX 4296 4168,
.CX 4425 4168,
.measureX 4425 [] [.CZ 4295 4167,.CZ 4295 4424,.CZ 4167 4424],
.CX 4295 4167,
.CX 4424 4167,
.measureX 4424 [] [.CZ 4294 4166,.CZ 4294 4423,.CZ 4166 4423],
.CX 4294 4166,
.CX 4423 4166,
.measureX 4423 [] [.CZ 4293 4165,.CZ 4293 4422,.CZ 4165 4422],
.CX 4293 4165,
.CX 4422 4165,
.measureX 4422 [] [.CZ 4292 4164,.CZ 4292 4421,.CZ 4164 4421],
.CX 4292 4164,
.CX 4421 4164,
.measureX 4421 [] [.CZ 4291 4163,.CZ 4291 4420,.CZ 4163 4420],
.CX 4291 4163,
.CX 4420 4163,
.measureX 4420 [] [.CZ 4290 4162,.CZ 4290 4419,.CZ 4162 4419],
.CX 4290 4162,
.CX 4419 4162,
.measureX 4419 [] [.CZ 4289 4161,.CZ 4289 4418,.CZ 4161 4418],
.CX 4289 4161,
.CX 4418 4161,
.measureX 4418 [] [.CZ 4288 4160,.CZ 4288 4417,.CZ 4160 4417],
.CX 4288 4160,
.CX 4417 4160,
.measureX 4417 [] [.CZ 4287 4159,.CZ 4287 4416,.CZ 4159 4416],
.CX 4287 4159,
.CX 4416 4159,
.measureX 4416 [] [.CZ 4286 4158,.CZ 4286 4415,.CZ 4158 4415]
]
def chunk8 : Program := [
.CX 4286 4158,
.CX 4415 4158,
.measureX 4415 [] [.CZ 4285 4157,.CZ 4285 4414,.CZ 4157 4414],
.CX 4285 4157,
.CX 4414 4157,
.measureX 4414 [] [.CZ 4284 4156,.CZ 4284 4413,.CZ 4156 4413],
.CX 4284 4156,
.CX 4413 4156,
.measureX 4413 [] [.CZ 4283 4155,.CZ 4283 4412,.CZ 4155 4412],
.CX 4283 4155,
.CX 4412 4155,
.measureX 4412 [] [.CZ 4282 4154,.CZ 4282 4411,.CZ 4154 4411],
.CX 4282 4154,
.CX 4411 4154,
.measureX 4411 [] [.CZ 4281 4153,.CZ 4281 4410,.CZ 4153 4410],
.CX 4281 4153,
.CX 4410 4153,
.measureX 4410 [] [.CZ 4280 4152,.CZ 4280 4409,.CZ 4152 4409],
.CX 4280 4152,
.CX 4409 4152,
.measureX 4409 [] [.CZ 4279 4151,.CZ 4279 4408,.CZ 4151 4408],
.CX 4279 4151,
.CX 4408 4151,
.measureX 4408 [] [.CZ 4278 4150,.CZ 4278 4407,.CZ 4150 4407],
.CX 4278 4150,
.CX 4407 4150,
.measureX 4407 [] [.CZ 4277 4149,.CZ 4277 4406,.CZ 4149 4406],
.CX 4277 4149,
.CX 4406 4149,
.measureX 4406 [] [.CZ 4276 4148,.CZ 4276 4405,.CZ 4148 4405],
.CX 4276 4148,
.CX 4405 4148,
.measureX 4405 [] [.CZ 4275 4147,.CZ 4275 4404,.CZ 4147 4404],
.CX 4275 4147,
.CX 4404 4147,
.measureX 4404 [] [.CZ 4274 4146,.CZ 4274 4403,.CZ 4146 4403],
.CX 4274 4146,
.CX 4403 4146,
.measureX 4403 [] [.CZ 4273 4145,.CZ 4273 4402,.CZ 4145 4402],
.CX 4273 4145,
.CX 4402 4145,
.measureX 4402 [] [.CZ 4272 4144,.CZ 4272 4401,.CZ 4144 4401],
.CX 4272 4144,
.CX 4401 4144,
.measureX 4401 [] [.CZ 4271 4143,.CZ 4271 4400,.CZ 4143 4400],
.CX 4271 4143,
.CX 4400 4143,
.measureX 4400 [] [.CZ 4270 4142,.CZ 4270 4399,.CZ 4142 4399],
.CX 4270 4142,
.CX 4399 4142,
.measureX 4399 [] [.CZ 4269 4141,.CZ 4269 4398,.CZ 4141 4398],
.CX 4269 4141,
.CX 4398 4141,
.measureX 4398 [] [.CZ 4268 4140,.CZ 4268 4397,.CZ 4140 4397],
.CX 4268 4140,
.CX 4397 4140,
.measureX 4397 [] [.CZ 4267 4139,.CZ 4267 4396,.CZ 4139 4396],
.CX 4267 4139,
.CX 4396 4139,
.measureX 4396 [] [.CZ 4266 4138,.CZ 4266 4395,.CZ 4138 4395],
.CX 4266 4138,
.CX 4395 4138,
.measureX 4395 [] [.CZ 4265 4137,.CZ 4265 4394,.CZ 4137 4394],
.CX 4265 4137,
.CX 4394 4137,
.measureX 4394 [] [.CZ 4264 4136,.CZ 4264 4393,.CZ 4136 4393],
.CX 4264 4136,
.CX 4393 4136,
.measureX 4393 [] [.CZ 4263 4135,.CZ 4263 4392,.CZ 4135 4392],
.CX 4263 4135,
.CX 4392 4135,
.measureX 4392 [] [.CZ 4262 4134,.CZ 4262 4391,.CZ 4134 4391],
.CX 4262 4134,
.CX 4391 4134,
.measureX 4391 [] [.CZ 4261 4133,.CZ 4261 4390,.CZ 4133 4390],
.CX 4261 4133,
.CX 4390 4133,
.measureX 4390 [] [.CZ 4260 4132,.CZ 4260 4389,.CZ 4132 4389],
.CX 4260 4132,
.CX 4389 4132,
.measureX 4389 [] [.CZ 4259 4131,.CZ 4259 4388,.CZ 4131 4388],
.CX 4259 4131,
.CX 4388 4131,
.measureX 4388 [] [.CZ 4258 4130,.CZ 4258 4387,.CZ 4130 4387],
.CX 4258 4130,
.CX 4387 4130,
.measureX 4387 [] [.CZ 4257 4129,.CZ 4257 4386,.CZ 4129 4386],
.CX 4257 4129,
.CX 4386 4129,
.measureX 4386 [] [.CZ 4256 4128,.CZ 4256 4385,.CZ 4128 4385],
.CX 4256 4128,
.CX 4385 4128,
.measureX 4385 [] [.CZ 4255 4127,.CZ 4255 4384,.CZ 4127 4384],
.CX 4255 4127,
.CX 4384 4127,
.measureX 4384 [] [.CZ 4254 4126,.CZ 4254 4383,.CZ 4126 4383],
.CX 4254 4126,
.CX 4383 4126,
.measureX 4383 [] [.CZ 4253 4125,.CZ 4253 4382,.CZ 4125 4382],
.CX 4253 4125,
.CX 4382 4125,
.measureX 4382 [] [.CZ 4252 4124,.CZ 4252 4381,.CZ 4124 4381],
.CX 4252 4124,
.CX 4381 4124,
.measureX 4381 [] [.CZ 4251 4123,.CZ 4251 4380,.CZ 4123 4380],
.CX 4251 4123,
.CX 4380 4123,
.measureX 4380 [] [.CZ 4250 4122,.CZ 4250 4379,.CZ 4122 4379],
.CX 4250 4122,
.CX 4379 4122,
.measureX 4379 [] [.CZ 4249 4121,.CZ 4249 4378,.CZ 4121 4378],
.CX 4249 4121,
.CX 4378 4121,
.measureX 4378 [] [.CZ 4248 4120,.CZ 4248 4377,.CZ 4120 4377],
.CX 4248 4120,
.CX 4377 4120,
.measureX 4377 [] [.CZ 4247 4119,.CZ 4247 4376,.CZ 4119 4376],
.CX 4247 4119,
.CX 4376 4119,
.measureX 4376 [] [.CZ 4246 4118,.CZ 4246 4375,.CZ 4118 4375],
.CX 4246 4118,
.CX 4375 4118,
.measureX 4375 [] [.CZ 4245 4117,.CZ 4245 4374,.CZ 4117 4374],
.CX 4245 4117,
.CX 4374 4117,
.measureX 4374 [] [.CZ 4244 4116,.CZ 4244 4373,.CZ 4116 4373],
.CX 4244 4116,
.CX 4373 4116
]
def chunk9 : Program := [
.measureX 4373 [] [.CZ 4243 4115,.CZ 4243 4760,.CZ 4115 4760],
.CX 4243 4115,
.CX 4760 4115,
.measureX 4764 [] [],
.X 4115,
.X 4116,
.X 4117,
.X 4118,
.X 4119,
.X 4120,
.X 4121,
.X 4122,
.X 4123,
.X 4124,
.X 4125,
.X 4126,
.X 4127,
.X 4128,
.X 4129,
.X 4130,
.X 4131,
.X 4132,
.X 4133,
.X 4134,
.X 4135,
.X 4136,
.X 4137,
.X 4138,
.X 4139,
.X 4140,
.X 4141,
.X 4142,
.X 4143,
.X 4144,
.X 4145,
.X 4146,
.CX 4340 4373,
.CX 4116 4373,
.X 4373,
.CX 4340 4116,
.CX 4340 4373,
.CCX 4116 4373 4374,
.CX 4340 4374,
.CX 4340 4373,
.CX 4340 4116,
.CX 4341 4117,
.CX 4341 4374,
.CCX 4117 4374 4375,
.CX 4341 4375,
.CX 4341 4374,
.CX 4341 4117,
.CX 4342 4118,
.CX 4342 4375,
.CCX 4118 4375 4376,
.CX 4342 4376,
.CX 4342 4375,
.CX 4342 4118,
.CX 4343 4119,
.CX 4343 4376,
.CCX 4119 4376 4377,
.CX 4343 4377,
.CX 4343 4376,
.CX 4343 4119,
.CX 4344 4120,
.CX 4344 4377,
.CCX 4120 4377 4378,
.CX 4344 4378,
.CX 4344 4377,
.CX 4344 4120,
.CX 4345 4121,
.CX 4345 4378,
.CCX 4121 4378 4379,
.CX 4345 4379,
.CX 4345 4378,
.CX 4345 4121,
.CX 4346 4122,
.CX 4346 4379,
.CCX 4122 4379 4380,
.CX 4346 4380,
.CX 4346 4379,
.CX 4346 4122,
.CX 4347 4123,
.CX 4347 4380,
.CCX 4123 4380 4381,
.CX 4347 4381,
.CX 4347 4380,
.CX 4347 4123,
.CX 4348 4124,
.CX 4348 4381,
.CCX 4124 4381 4382,
.CX 4348 4382,
.CX 4348 4381,
.CX 4348 4124,
.CX 4349 4125,
.CX 4349 4382,
.CCX 4125 4382 4383,
.CX 4349 4383,
.CX 4349 4382,
.CX 4349 4125,
.CX 4350 4126,
.CX 4350 4383,
.CCX 4126 4383 4384,
.CX 4350 4384,
.CX 4350 4383,
.CX 4350 4126,
.CX 4351 4127,
.CX 4351 4384,
.CCX 4127 4384 4385,
.CX 4351 4385,
.CX 4351 4384,
.CX 4351 4127,
.CX 4352 4128,
.CX 4352 4385,
.CCX 4128 4385 4386,
.CX 4352 4386,
.CX 4352 4385,
.CX 4352 4128,
.CX 4353 4129,
.CX 4353 4386,
.CCX 4129 4386 4387,
.CX 4353 4387,
.CX 4353 4386,
.CX 4353 4129,
.CX 4354 4130,
.CX 4354 4387,
.CCX 4130 4387 4388,
.CX 4354 4388,
.CX 4354 4387
]
def chunk10 : Program := [
.CX 4354 4130,
.CX 4355 4131,
.CX 4355 4388,
.CCX 4131 4388 4389,
.CX 4355 4389,
.CX 4355 4388,
.CX 4355 4131,
.CX 4356 4132,
.CX 4356 4389,
.CCX 4132 4389 4390,
.CX 4356 4390,
.CX 4356 4389,
.CX 4356 4132,
.CX 4357 4133,
.CX 4357 4390,
.CCX 4133 4390 4391,
.CX 4357 4391,
.CX 4357 4390,
.CX 4357 4133,
.CX 4358 4134,
.CX 4358 4391,
.CCX 4134 4391 4392,
.CX 4358 4392,
.CX 4358 4391,
.CX 4358 4134,
.CX 4359 4135,
.CX 4359 4392,
.CCX 4135 4392 4393,
.CX 4359 4393,
.CX 4359 4392,
.CX 4359 4135,
.CX 4360 4136,
.CX 4360 4393,
.CCX 4136 4393 4394,
.CX 4360 4394,
.CX 4360 4393,
.CX 4360 4136,
.CX 4361 4137,
.CX 4361 4394,
.CCX 4137 4394 4395,
.CX 4361 4395,
.CX 4361 4394,
.CX 4361 4137,
.CX 4362 4138,
.CX 4362 4395,
.CCX 4138 4395 4396,
.CX 4362 4396,
.CX 4362 4395,
.CX 4362 4138,
.CX 4363 4139,
.CX 4363 4396,
.CCX 4139 4396 4397,
.CX 4363 4397,
.CX 4363 4396,
.CX 4363 4139,
.CX 4364 4140,
.CX 4364 4397,
.CCX 4140 4397 4398,
.CX 4364 4398,
.CX 4364 4397,
.CX 4364 4140,
.CX 4365 4141,
.CX 4365 4398,
.CCX 4141 4398 4399,
.CX 4365 4399,
.CX 4365 4398,
.CX 4365 4141,
.CX 4366 4142,
.CX 4366 4399,
.CCX 4142 4399 4400,
.CX 4366 4400,
.CX 4366 4399,
.CX 4366 4142,
.CX 4367 4143,
.CX 4367 4400,
.CCX 4143 4400 4401,
.CX 4367 4401,
.CX 4367 4400,
.CX 4367 4143,
.CX 4368 4144,
.CX 4368 4401,
.CCX 4144 4401 4402,
.CX 4368 4402,
.CX 4368 4401,
.CX 4368 4144,
.CX 4369 4145,
.CX 4369 4402,
.CCX 4145 4402 4403,
.CX 4369 4403,
.CX 4369 4402,
.CX 4369 4145,
.measureX 4763 [] [.CZ 4370 4146,.CZ 4370 4403,.CZ 4146 4403],
.CX 4370 4146,
.CX 4403 4146,
.measureX 4403 [] [.CZ 4369 4145,.CZ 4369 4402,.CZ 4145 4402],
.CX 4369 4145,
.CX 4402 4145,
.measureX 4402 [] [.CZ 4368 4144,.CZ 4368 4401,.CZ 4144 4401],
.CX 4368 4144,
.CX 4401 4144,
.measureX 4401 [] [.CZ 4367 4143,.CZ 4367 4400,.CZ 4143 4400],
.CX 4367 4143,
.CX 4400 4143,
.measureX 4400 [] [.CZ 4366 4142,.CZ 4366 4399,.CZ 4142 4399],
.CX 4366 4142,
.CX 4399 4142,
.measureX 4399 [] [.CZ 4365 4141,.CZ 4365 4398,.CZ 4141 4398],
.CX 4365 4141,
.CX 4398 4141,
.measureX 4398 [] [.CZ 4364 4140,.CZ 4364 4397,.CZ 4140 4397],
.CX 4364 4140,
.CX 4397 4140,
.measureX 4397 [] [.CZ 4363 4139,.CZ 4363 4396,.CZ 4139 4396],
.CX 4363 4139,
.CX 4396 4139,
.measureX 4396 [] [.CZ 4362 4138,.CZ 4362 4395,.CZ 4138 4395],
.CX 4362 4138,
.CX 4395 4138,
.measureX 4395 [] [.CZ 4361 4137,.CZ 4361 4394,.CZ 4137 4394],
.CX 4361 4137,
.CX 4394 4137,
.measureX 4394 [] [.CZ 4360 4136,.CZ 4360 4393,.CZ 4136 4393],
.CX 4360 4136,
.CX 4393 4136,
.measureX 4393 [] [.CZ 4359 4135,.CZ 4359 4392,.CZ 4135 4392],
.CX 4359 4135,
.CX 4392 4135,
.measureX 4392 [] [.CZ 4358 4134,.CZ 4358 4391,.CZ 4134 4391]
]
def chunk11 : Program := [
.CX 4358 4134,
.CX 4391 4134,
.measureX 4391 [] [.CZ 4357 4133,.CZ 4357 4390,.CZ 4133 4390],
.CX 4357 4133,
.CX 4390 4133,
.measureX 4390 [] [.CZ 4356 4132,.CZ 4356 4389,.CZ 4132 4389],
.CX 4356 4132,
.CX 4389 4132,
.measureX 4389 [] [.CZ 4355 4131,.CZ 4355 4388,.CZ 4131 4388],
.CX 4355 4131,
.CX 4388 4131,
.measureX 4388 [] [.CZ 4354 4130,.CZ 4354 4387,.CZ 4130 4387],
.CX 4354 4130,
.CX 4387 4130,
.measureX 4387 [] [.CZ 4353 4129,.CZ 4353 4386,.CZ 4129 4386],
.CX 4353 4129,
.CX 4386 4129,
.measureX 4386 [] [.CZ 4352 4128,.CZ 4352 4385,.CZ 4128 4385],
.CX 4352 4128,
.CX 4385 4128,
.measureX 4385 [] [.CZ 4351 4127,.CZ 4351 4384,.CZ 4127 4384],
.CX 4351 4127,
.CX 4384 4127,
.measureX 4384 [] [.CZ 4350 4126,.CZ 4350 4383,.CZ 4126 4383],
.CX 4350 4126,
.CX 4383 4126,
.measureX 4383 [] [.CZ 4349 4125,.CZ 4349 4382,.CZ 4125 4382],
.CX 4349 4125,
.CX 4382 4125,
.measureX 4382 [] [.CZ 4348 4124,.CZ 4348 4381,.CZ 4124 4381],
.CX 4348 4124,
.CX 4381 4124,
.measureX 4381 [] [.CZ 4347 4123,.CZ 4347 4380,.CZ 4123 4380],
.CX 4347 4123,
.CX 4380 4123,
.measureX 4380 [] [.CZ 4346 4122,.CZ 4346 4379,.CZ 4122 4379],
.CX 4346 4122,
.CX 4379 4122,
.measureX 4379 [] [.CZ 4345 4121,.CZ 4345 4378,.CZ 4121 4378],
.CX 4345 4121,
.CX 4378 4121,
.measureX 4378 [] [.CZ 4344 4120,.CZ 4344 4377,.CZ 4120 4377],
.CX 4344 4120,
.CX 4377 4120,
.measureX 4377 [] [.CZ 4343 4119,.CZ 4343 4376,.CZ 4119 4376],
.CX 4343 4119,
.CX 4376 4119,
.measureX 4376 [] [.CZ 4342 4118,.CZ 4342 4375,.CZ 4118 4375],
.CX 4342 4118,
.CX 4375 4118,
.measureX 4375 [] [.CZ 4341 4117,.CZ 4341 4374,.CZ 4117 4374],
.CX 4341 4117,
.CX 4374 4117,
.measureX 4374 [] [.CZ 4340 4116,.CZ 4340 4373,.CZ 4116 4373],
.CX 4340 4116,
.CX 4373 4116,
.measureX 4373 [] [.CZ 4339 4115,.CZ 4339 4760,.CZ 4115 4760],
.CX 4339 4115,
.CX 4760 4115,
.X 4115,
.X 4116,
.X 4117,
.X 4118,
.X 4119,
.X 4120,
.X 4121,
.X 4122,
.X 4123,
.X 4124,
.X 4125,
.X 4126,
.X 4127,
.X 4128,
.X 4129,
.X 4130,
.X 4131,
.X 4132,
.X 4133,
.X 4134,
.X 4135,
.X 4136,
.X 4137,
.X 4138,
.X 4139,
.X 4140,
.X 4141,
.X 4142,
.X 4143,
.X 4144,
.X 4145,
.X 4146,
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk12 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk13 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk14 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk15 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk16 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def chunk17 : Program := [
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] [],
.measureX 4764 [] []
]
def program : Program := ((((chunk0++chunk1)++(chunk2++chunk3))++((chunk4++chunk5)++(chunk6++(chunk7++chunk8))))++(((chunk9++chunk10)++(chunk11++chunk12))++((chunk13++chunk14)++(chunk15++(chunk16++chunk17)))))
def actual : Program := ParkCarry10Develop.rebuild LowAccCarryDevelop.L
theorem literal : actual=program := by
 apply ParkAProgramBool.programEq_sound
 decide +kernel
theorem length : actual.length=2243 := by rw [literal];decide +kernel
attribute [local irreducible] actual program prefixState run

def window : Program := [.CCX 4242 4499 4500,.CX 4370 4500,.CX 4370 4499,.CX 4370 4242,
 .measureX 4372 [] [.CZ 4765 4371,.CZ 4765 4500,.CZ 4371 4500],.CX 4765 4371,.CX 4500 4371]
def repair : Program := [.CX 4371 4500,.CX 4370 4500]
def improved : Program := SixCarryPatchGeneric.patch actual 764 repair
attribute [local irreducible] improved

theorem lookup : actual[764]?=some (.CCX 4242 4499 4500) := by rw [literal];decide +kernel
theorem no_t : noWriteBetween actual 0 764 4500=true := by rw [literal];decide +kernel
theorem no_v : noWriteBetween actual 0 764 4765=true := by rw [literal];decide +kernel
theorem no_out : noWriteBetween actual 771 actual.length 4371=true := by rw [literal];decide +kernel
theorem window_eq : (actual.drop 764).take 7=window := by rw [literal];decide +kernel

theorem window_from_output (b : BasisState) (ht : b 4500=false) (hv : b 4765=false)
 (hout : basisRun window b 4371=false) : (b 4242 && b 4499)=(b 4371 ^^ b 4370) := by
 have h : (b 4371 ^^ ((b 4242 && b 4499) ^^ b 4370))=false := by
  simpa [window,basisRun,basisStep,writeBit,ht,hv] using hout
 cases ha : b 4242 <;> cases hb : b 4499 <;> cases hu : b 4371 <;> cases hc : b 4370 <;> simp_all

theorem window_state (b : BasisState) :
 prefixState actual 771 b=basisRun window (prefixState actual 764 b) := by
 unfold prefixState
 change basisRun (actual.take (764+7)) b=_
 rw [List.take_add,basisRun_append,window_eq]

theorem condition (b : BasisState) (ht : b 4500=false) (hv : b 4765=false)
 (hout : basisRun actual b 4371=false) :
 let v:=prefixState actual 764 b
 (v 4242 && v 4499)=(v 4371 ^^ v 4370) := by
 have a:=at_between actual 0 764 4500 (by decide +kernel) no_t b
 have c:=at_between actual 0 764 4765 (by decide +kernel) no_v b
 have a0:prefixState actual 764 b 4500=b 4500 := by simpa only [prefixState,List.take_zero,basisRun] using a
 have c0:prefixState actual 764 b 4765=b 4765 := by simpa only [prefixState,List.take_zero,basisRun] using c
 have zt:prefixState actual 764 b 4500=false := a0.trans ht
 have zv:prefixState actual 764 b 4765=false := c0.trans hv
 have h:=at_between actual 771 actual.length 4371 (by rw [length];decide +kernel) no_out b
 rw [at_full,hout,window_state] at h
 exact window_from_output _ zt zv h.symm

theorem gate (s : State) (m : List Bool)
 (h : (s.basis 4242 && s.basis 4499)=(s.basis 4371 ^^ s.basis 4370)) :
 run [.CCX 4242 4499 4500] m s=run repair m s := by
 have hv:=congrArg (fun z=>s.basis 4500 ^^ z) h
 apply state_ext
 · simp [run,repair]
 · funext q
   by_cases hq:q=4500
   · subst q
     simpa [run,repair,writeBit,Function.update_apply,Bool.xor_assoc] using hv
   · simp [run,repair,writeBit,hq]

theorem run_eq (s : State) (m : List Bool) (ht : s.basis 4500=false) (hv : s.basis 4765=false)
 (hout : (run actual m s).basis 4371=false) : run actual m s=run improved m s := by
 have h:basisRun actual s.basis 4371=false := by simpa only [run_basis] using hout
 unfold improved
 apply SixCarryPatchGeneric.run_eq actual 764 4242 4499 4500 repair lookup (by decide +kernel) s m
 apply gate
 simpa only [prefixState,run_basis] using condition s.basis ht hv h
#print axioms run_eq
end ECDSAAdd.Entrant.LocalRebuild

end

section
-- Preserved checked rebuild component: LocalRebuildResources
namespace ECDSAAdd.Entrant.LocalRebuildResources
open ECDSAAdd Arithmetic Challenge LocalRebuild SixCarryPatchGeneric
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] actual improved toffoliCount measurementCount gateSlots wires
 theorem shape : improved=patch actual 764 repair := by unfold improved;rfl
 theorem toffoli : toffoliCount improved+1=toffoliCount actual :=
 Eq.mp (congrArg (fun p=>toffoliCount p+1=toffoliCount actual) shape.symm)
  (SixCarryPatchResources.toffoli actual 764 4242 4499 4500 repair lookup (by decide +kernel))
 theorem measurements : measurementCount improved=measurementCount actual :=
 Eq.mp (congrArg (fun p=>measurementCount p=measurementCount actual) shape.symm)
  (SixCarryPatchResources.measurements actual 764 4242 4499 4500 repair lookup (by decide +kernel))
 theorem slots : gateSlots improved=gateSlots actual+1 :=
 Eq.mp (congrArg (fun p=>gateSlots p=gateSlots actual+1) shape.symm)
  (SixCarryPatchResources.slots actual 764 4242 4499 4500 repair 1 lookup (by decide +kernel))
 theorem repair_subset : wires repair⊆wires actual := by
  have small : wires repair⊆wires window := by
   intro q hq
   simp [repair,window,wires,Instr.wires,correctionWires] at hq ⊢
   tauto
  have shapeWindow : actual=actual.take 764++(window++actual.drop 771) := by
   calc actual=actual.take 771++actual.drop 771 := (List.take_append_drop 771 actual).symm
        _ =(actual.take 764++window)++actual.drop 771 := by
         congr 1
         change actual.take (764+7)=_
         rw [List.take_add,window_eq]
        _ =actual.take 764++(window++actual.drop 771) := List.append_assoc _ _ _
  have sub:wires window⊆wires actual := by
   rw [shapeWindow,wires_append,wires_append]
   exact Finset.subset_union_left.trans Finset.subset_union_right
  exact small.trans sub
 theorem support : wires improved⊆wires actual :=
 Eq.mp (congrArg (fun p=>wires p⊆wires actual) shape.symm)
  (SixCarryPatchSupport.support actual 764 (.CCX 4242 4499 4500) repair lookup repair_subset)
 theorem physical (hp : GatePhysical actual) : GatePhysical improved :=
 Eq.mp (congrArg GatePhysical shape.symm)
  (SixCarryPatchSupport.physical actual 764 (.CCX 4242 4499 4500) repair lookup hp
   (physicalGateCheck_correct repair (by decide +kernel)))
#print axioms toffoli
#print axioms support
end ECDSAAdd.Entrant.LocalRebuildResources

end

section
-- Preserved checked rebuild component: LocalRebuildLift
namespace ECDSAAdd.Entrant.LocalRebuildLift
open ECDSAAdd Arithmetic ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
abbrev L := LowAccCarryDevelop.L

theorem transfer (base outBase : BasisState) (clean : L.PairClean base) (O E B : Nat)
 (hb : B<2^128)
 (old : Triple (BState L base O E 0) (ParkCarry10Develop.rebuild L) (BState L outBase O B 0)) :
 Triple (BState L base O E 0) LocalRebuild.improved (BState L outBase O B 0) := by
 intro s m hs
 have c:=bstate_clean L LowAccCarryDevelop.layout_nodup base clean O E s.basis hs
 have ht:s.basis 4500=false := (regValue_zero _ _).mp c.pad 4500 (by decide +kernel)
 have hv:s.basis 4765=false := (regValue_zero _ _).mp c.pad 4765 (by decide +kernel)
 have out:=old s m hs
 have bit:=LocalEFoldInputs.bit128 _ B out.2.2.1
 rw [Nat.div_eq_of_lt hb] at bit
 have z:(run (ParkCarry10Develop.rebuild L) m s).basis 4371=false := by
  cases h:(run (ParkCarry10Develop.rebuild L) m s).basis 4371 <;> simp_all
 have eq:=LocalRebuild.run_eq s m ht hv z
 rw [←eq]
 simpa only [LocalRebuild.actual] using out
#print axioms transfer
end ECDSAAdd.Entrant.LocalRebuildLift

end

section
-- Preserved checked rebuild component: LocalRebuildBody
namespace ECDSAAdd.Entrant.LocalRebuildBody
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop LowAccCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
def bodyForBoth (L : CuccaroStreamedSquareWideLayout) (loop fold rebuild : Program) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldFor L loop ++ (fold ++ rebuild)))
theorem frame
 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (loopProgram : Program)
 (loopSpec : ∀ (base : BasisState) (_clean : L.PairClean base) (_hsum : base L.core.sumCarry=false)
  (O E O' : Nat),
  Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
   (BState L base O' E (4294968272*regValue (hiReg L) base)) →
  Triple (BState L base O E 0) loopProgram (BState L base O' E 0))
 (foldProgram : Program)
 (foldSpec : ∀ (base : BasisState) (_clean : L.PairClean base) (O E : Nat)
  (_hO : O<SquareReduction.p) (_hE : E<2^130)
  (_hRange : E<2^128 ∨ 2^130-2^128≤E)
  (_hOff : base c=false → E=0) (Q : BasisState→Prop),
  Triple (BState L base O E 0) (eFoldTq L c) Q →
  Triple (BState L base O E 0) foldProgram Q)
 (rebuildProgram : Program)
 (rebuildSpec : ∀ (base outBase : BasisState) (_clean : L.PairClean base) (O E B : Nat)
  (_hb : B<2^128),
  Triple (BState L base O E 0) (ParkCarry10Develop.rebuild L) (BState L outBase O B 0) →
  Triple (BState L base O E 0) rebuildProgram (BState L outBase O B 0))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyForBoth L loopProgram foldProgram rebuildProgram)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by

  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := ParkCarryDevelop.base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply ParkCarryDevelop.sumCarry_away L hn;simp [ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [ParkCarryDevelop.reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have source0:base (L.core.high.headD 0)=digit originalM 0:=by
    simpa only[digit,pow_zero,Nat.div_one]using head_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE2:(2^32*H+l'+2^128*K)%2=lowSum (base c) originalM u%2:=by omega
  have loanFact0:=LowBitCarryNumbers.loan0_from_mod2 (base c) originalM u (2^32*H+l'+2^128*K)
    (by simpa only[lowSum]using modE2)
  rw[←source0]at loanFact0
  have wm := wMidFullCCC0_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact0
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC0 L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have loop := loopSpec base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (foldFor L loopProgram) (BState L baseK O3 E1 0) :=
    by simpa only [foldFor,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
  have hA : 2^32*H+l'<2^128 := by
    have hH0:=hH
    have hl0:=hl'
    norm_num at hH0 hl0 ⊢
    omega
  have hEbound : E1<2^130 := Nat.mod_lt _ (by positivity)
  have hErange : E1<2^128 ∨ 2^130-2^128≤E1 :=
    LocalEFoldInputs.range (2^32*H+l') b1 hA hb1lt
  have hEoff : baseK c=false → E1=0 := by
    intro hc0
    have m0 : M=0 := hg (gc.symm.trans hc0)
    simp [E1,H,l',b0,b1,P,u,m0]
  have tfNew : Triple (BState L baseK O3 E1 0) foldProgram (BState L baseK O4 E1 0) :=
    foldSpec baseK hcK O3 E1 hO3 hEbound hErange hEoff _ tf
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=ParkCarryDevelop.restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (ParkCarry10Develop.rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have trNew : Triple (BState L baseK O4 E1 0) rebuildProgram (BState L base O4 b0 0) :=
    rebuildSpec baseK base hcK O4 E1 b0 hb0 tr
  have conv0 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tfNew.seq trNew)) conv0))
  rw [key] at all
  simpa only [bodyForBoth] using all


#print axioms frame
end ECDSAAdd.Entrant.LocalRebuildBody

end

section
-- Preserved checked rebuild component: LocalRebuildBody91
namespace ECDSAAdd.Entrant.LocalRebuildBody91
open ECDSAAdd Arithmetic Challenge ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
abbrev L := LowAccCarryDevelop.L
abbrev c := LowAccCarryDevelop.c
abbrev CM := ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c)
def bodyWith (cm : CM) : Program :=
 LocalRebuildBody.bodyForBoth L (LowAccCarryDevelop.loopWith cm) LocalEFoldOptimize.improved LocalRebuild.improved

theorem frame (cm : CM)
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum : base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyWith cm)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
 unfold bodyWith
 apply LocalRebuildBody.frame L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup c
  LowAccCarryDevelop.control_outside (LowAccCarryDevelop.loopWith cm) (LowAccCarryDevelop.loop_bstate_step cm)
  LocalEFoldOptimize.improved ?_ LocalRebuild.improved ?_ base M hM hP hc hsum O hO hg hSource
 · intro b clean O0 E0 _ eb er off Q old
   exact LocalEFoldLift.transfer b clean O0 E0 eb er off Q old
 · intro b outB clean O0 E0 B0 hb old
   exact LocalRebuildLift.transfer b outB clean O0 E0 B0 hb old
#print axioms frame
end ECDSAAdd.Entrant.LocalRebuildBody91

end

section
-- Preserved checked rebuild component: LocalRebuildBody91Costs
namespace ECDSAAdd.Entrant.LocalRebuildBody91Costs
open ECDSAAdd Arithmetic Challenge LocalRebuildBody91
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] toffoliCount measurementCount gateSlots wires

theorem old_shape (cm : CM) : LocalEFoldBody90.bodyWith cm=
 LocalEFoldBody90Costs.pre cm++(LocalEFoldOptimize.improved++LocalRebuild.actual) := by
 simpa only [LocalEFoldBody90Costs.post,LocalRebuild.actual] using LocalEFoldBody90Costs.new_shape cm

theorem new_shape (cm : CM) : bodyWith cm=
 LocalEFoldBody90Costs.pre cm++(LocalEFoldOptimize.improved++LocalRebuild.improved) := by
 simp only [bodyWith,LocalRebuildBody.bodyForBoth,LocalEFoldBody90Costs.pre,List.append_assoc]

theorem toffoli (cm : CM) : toffoliCount (bodyWith cm)+1=toffoliCount (LocalEFoldBody90.bodyWith cm) := by
 rw [old_shape,new_shape]
 simp only [toffoliCount_append]
 have h:=LocalRebuildResources.toffoli
 omega

theorem measurements (cm : CM) : measurementCount (bodyWith cm)=measurementCount (LocalEFoldBody90.bodyWith cm) := by
 rw [old_shape,new_shape]
 simp only [measurementCount_append,LocalRebuildResources.measurements]

theorem slots (cm : CM) : gateSlots (bodyWith cm)=gateSlots (LocalEFoldBody90.bodyWith cm)+1 := by
 rw [old_shape,new_shape]
 simp only [gateSlots_append]
 have h:=LocalRebuildResources.slots
 omega

theorem resources (cm : CM) :
 toffoliCount (bodyWith cm)+91≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount (bodyWith cm)=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 gateSlots (bodyWith cm)+263≤gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 have old:=LocalEFoldBody90Costs.resources cm
 dsimp only [LocalEFoldBody90.L,LocalEFoldBody90.c] at old
 have t:=toffoli cm
 have m:=measurements cm
 have g:=slots cm
 exact ⟨by omega,m.trans old.2.1,by omega⟩

theorem support (cm : CM) : wires (bodyWith cm)⊆wires (LocalEFoldBody90.bodyWith cm) := by
 rw [new_shape,old_shape,wires_append,wires_append,wires_append,wires_append]
 exact Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union (Finset.Subset.refl _) LocalRebuildResources.support)

theorem support_old (cm : CM) : wires (bodyWith cm)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) :=
 (support cm).trans ((LocalEFoldBody90Costs.support cm).trans (LowAccCarryDevelop.body_support cm))

theorem physical (cm : CM) : GatePhysical (bodyWith cm) := by
 have h:=LocalEFoldBody90Costs.physical cm
 rw [old_shape,gatePhysical_append,gatePhysical_append] at h
 rw [new_shape,gatePhysical_append,gatePhysical_append]
 exact ⟨h.1,h.2.1,LocalRebuildResources.physical h.2.2⟩
#print axioms resources
#print axioms physical
end ECDSAAdd.Entrant.LocalRebuildBody91Costs

end

section
-- Preserved checked rebuild component: LocalRebuildSelector91
namespace ECDSAAdd.Entrant.FullB91FoldOptTemp
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.Arithmetic.GatePhysical
attribute [local irreducible] ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots ECDSAAdd.regValue
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem option_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hf : P fallback) (hb : ∀a,P (body a)) (result : Option α) : P (result.elim fallback body) := by
 cases result with
 | none => exact hf
 | some a => exact hb a

theorem option_some_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hb : ∀a,P (body a)) (result : Option α) (success : result.isSome=true) : P (result.elim fallback body) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at success
 | some a => exact hb a

theorem option_map_success {α β : Type} (result : Option α) (f : α → β) :
 (result.map f).isSome=result.isSome := by
 cases result <;> rfl

theorem actual_resources :
 toffoliCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith)+91≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith)=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith)+263≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_some_property (fun p=>
  toffoliCount p+91≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  measurementCount p=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  Challenge.gateSlots p+263≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith LocalRebuildBody91Costs.resources ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)
  ((option_map_success (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0) LowAccCarryDevelop.fromLiteral).trans LowAccCarryDevelop.success_literal)

theorem actual_subset : wires (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_property (fun p=>wires p⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith (Finset.Subset.refl (wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))) LocalRebuildBody91Costs.support_old ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_physical : GatePhysical (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith) := by
 exact option_property GatePhysical (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith
  (ParkCarry10Develop.body_physical LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.c LowAccCarryDevelop.layout_control_nodup)
  LocalRebuildBody91Costs.physical ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith)
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) := by
 exact option_property (fun p=>Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) p
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O))) (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith
  (ParkCarry10Develop.body_frame LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.layout_nodup LowAccCarryDevelop.c LowAccCarryDevelop.control_outside
   base M hM hP hc hsum O hO hg hSource)
  (fun cm=>LocalRebuildBody91.frame cm base M hM hP hc hsum O hO hg hSource) ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => ParkCarry10Develop.body K g
 | isTrue _ => if g=LowAccCarryDevelop.c then (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith) else ParkCarry10Develop.body K g

theorem selected_body_transport (K K' : CuccaroStreamedSquareWideLayout) (g g' : Wire)
 (he : K=K') (hg : g=g') : selectedBody K g=selectedBody K' g' := by
 cases he
 cases hg
 rfl

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 wires (selectedBody K g)⊆wires (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact Finset.Subset.refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_subset
  · exact Finset.Subset.refl _

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c)⊆(c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths)
 (g : Wire) (nd : (g::K.wires).Nodup) : GatePhysical (selectedBody K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ParkCarry10Develop.body_physical K hw g nd
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_physical
  · exact ParkCarry10Develop.body_physical K hw g nd

theorem selected_frame (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (hn : K.wires.Nodup)
 (g : Wire) (hcw : g∉K.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue K.core.product base=M^2) (hc : K.PairClean base)
 (hsum : base K.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base g=false → M=0) (hSource : M=if base g then regValue K.core.high base else 0) :
 Triple (SquareFrame K.core.out base O) (selectedBody K g)
  (SquareFrame K.core.out base (bO4 (M^2) (base g) O)) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hne => exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource
 | isTrue hl =>
  dsimp only
  split
  · rename_i hgc;subst K;subst g;exact actual_frame base M hM hP hc hsum O hO hg hSource
  · exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource

theorem selected_resources (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 toffoliCount (selectedBody K g)≤toffoliCount (ParkCarry10Develop.body K g) ∧
 measurementCount (selectedBody K g)=measurementCount (ParkCarry10Develop.body K g) ∧
 Challenge.gateSlots (selectedBody K g)≤Challenge.gateSlots (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g
    have h:=actual_resources
    exact ⟨by omega,h.2.1,by omega⟩
  · exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c=selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c)≤toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c)≤Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 selected_resources (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c)⊆wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

abbrev actualLayout := FullBOptTemp.actualLayout
abbrev actualControl := FullBOptTemp.actualControl
abbrev actualExt := FullBOptTemp.actualExt
abbrev actualFoldPerm := FullBOptTemp.actualFoldPerm

theorem selected_actual : selectedBody LowAccCarryDevelop.L LowAccCarryDevelop.c=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq LowAccCarryDevelop.L LowAccCarryDevelop.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

theorem ranked_selected_exact : hostedSelectedBody actualLayout actualFoldPerm actualControl=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LocalRebuildBody91.bodyWith) := by
 have he : ParkCarryDevelop.hostLayout actualLayout actualFoldPerm=actualLayout :=
  FullBOptTemp.actualHostedLayout_eq
 exact (congrArg (fun K=>selectedBody K actualControl) he).trans
  ((selected_body_transport actualLayout LowAccCarryDevelop.L actualControl LowAccCarryDevelop.c rfl rfl).trans selected_actual)

theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+91≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 := by
 rw [ranked_selected_exact]
 have h:=actual_resources
 have old:=ParkCarry10Develop.body_counts LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.c
 exact ⟨h.1.trans old.1.le,h.2.1.trans old.2⟩

end ECDSAAdd.Entrant.FullB91FoldOptTemp
#print axioms ECDSAAdd.Entrant.FullB91FoldOptTemp.actual_frame
#print axioms ECDSAAdd.Entrant.FullB91FoldOptTemp.ranked_certified_gain

end
