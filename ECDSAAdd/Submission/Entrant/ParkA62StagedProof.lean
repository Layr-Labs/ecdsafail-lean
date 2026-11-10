import ECDSAAdd.Submission.Entrant.ParkA62ManyBase
import ECDSAAdd.Submission.Entrant.ParkAStagedProof
import ECDSAAdd.Submission.Entrant.ParkA62Data
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ParkA62StagedProof

theorem append (qs rs : List Wire) (p r t : Program) (first : ParkAChain.Steps qs p r) :
 ParkAChain.Steps rs r t → ParkAChain.Steps (qs++rs) p t := by
 induction first with
 | nil p => exact fun last => last
 | cons q qs p r u head tail ih =>
   intro last
   exact ParkAChain.Steps.cons q (qs++rs) p r t head (ih last)

theorem input_eq : ParkAData.p0 =
 aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic := ParkAStagedProof.input_eq

theorem hosts_eq : ParkA62Many.loans Baselines.layout.dialogStreamedSquareWide =
 ParkAStagedProof.actualHosts++[4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] := by decide +kernel

theorem step33_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4728 ParkAData.p33).map (fun c => c.out))
 (some ParkA62Data.p34)=true := by decide +kernel

theorem step33_eq : ((compileChunked? 4728 ParkAData.p33).map (fun c => c.out))=
 some ParkA62Data.p34 := ParkAOptionBool.optionEq_sound _ _ step33_bool

theorem step34_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4729 ParkA62Data.p34).map (fun c => c.out))
 (some ParkA62Data.p35)=true := by decide +kernel

theorem step34_eq : ((compileChunked? 4729 ParkA62Data.p34).map (fun c => c.out))=
 some ParkA62Data.p35 := ParkAOptionBool.optionEq_sound _ _ step34_bool

theorem step35_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4730 ParkA62Data.p35).map (fun c => c.out))
 (some ParkA62Data.p36)=true := by decide +kernel

theorem step35_eq : ((compileChunked? 4730 ParkA62Data.p35).map (fun c => c.out))=
 some ParkA62Data.p36 := ParkAOptionBool.optionEq_sound _ _ step35_bool

theorem step36_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4731 ParkA62Data.p36).map (fun c => c.out))
 (some ParkA62Data.p37)=true := by decide +kernel

theorem step36_eq : ((compileChunked? 4731 ParkA62Data.p36).map (fun c => c.out))=
 some ParkA62Data.p37 := ParkAOptionBool.optionEq_sound _ _ step36_bool

theorem step37_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4732 ParkA62Data.p37).map (fun c => c.out))
 (some ParkA62Data.p38)=true := by decide +kernel

theorem step37_eq : ((compileChunked? 4732 ParkA62Data.p37).map (fun c => c.out))=
 some ParkA62Data.p38 := ParkAOptionBool.optionEq_sound _ _ step37_bool

theorem step38_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4733 ParkA62Data.p38).map (fun c => c.out))
 (some ParkA62Data.p39)=true := by decide +kernel

theorem step38_eq : ((compileChunked? 4733 ParkA62Data.p38).map (fun c => c.out))=
 some ParkA62Data.p39 := ParkAOptionBool.optionEq_sound _ _ step38_bool

theorem step39_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4734 ParkA62Data.p39).map (fun c => c.out))
 (some ParkA62Data.p40)=true := by decide +kernel

theorem step39_eq : ((compileChunked? 4734 ParkA62Data.p39).map (fun c => c.out))=
 some ParkA62Data.p40 := ParkAOptionBool.optionEq_sound _ _ step39_bool

theorem step40_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4735 ParkA62Data.p40).map (fun c => c.out))
 (some ParkA62Data.p41)=true := by decide +kernel

theorem step40_eq : ((compileChunked? 4735 ParkA62Data.p40).map (fun c => c.out))=
 some ParkA62Data.p41 := ParkAOptionBool.optionEq_sound _ _ step40_bool

theorem step41_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4736 ParkA62Data.p41).map (fun c => c.out))
 (some ParkA62Data.p42)=true := by decide +kernel

theorem step41_eq : ((compileChunked? 4736 ParkA62Data.p41).map (fun c => c.out))=
 some ParkA62Data.p42 := ParkAOptionBool.optionEq_sound _ _ step41_bool

theorem step42_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4737 ParkA62Data.p42).map (fun c => c.out))
 (some ParkA62Data.p43)=true := by decide +kernel

theorem step42_eq : ((compileChunked? 4737 ParkA62Data.p42).map (fun c => c.out))=
 some ParkA62Data.p43 := ParkAOptionBool.optionEq_sound _ _ step42_bool

theorem step43_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4738 ParkA62Data.p43).map (fun c => c.out))
 (some ParkA62Data.p44)=true := by decide +kernel

theorem step43_eq : ((compileChunked? 4738 ParkA62Data.p43).map (fun c => c.out))=
 some ParkA62Data.p44 := ParkAOptionBool.optionEq_sound _ _ step43_bool

theorem step44_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4739 ParkA62Data.p44).map (fun c => c.out))
 (some ParkA62Data.p45)=true := by decide +kernel

theorem step44_eq : ((compileChunked? 4739 ParkA62Data.p44).map (fun c => c.out))=
 some ParkA62Data.p45 := ParkAOptionBool.optionEq_sound _ _ step44_bool

theorem step45_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4740 ParkA62Data.p45).map (fun c => c.out))
 (some ParkA62Data.p46)=true := by decide +kernel

theorem step45_eq : ((compileChunked? 4740 ParkA62Data.p45).map (fun c => c.out))=
 some ParkA62Data.p46 := ParkAOptionBool.optionEq_sound _ _ step45_bool

theorem step46_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4741 ParkA62Data.p46).map (fun c => c.out))
 (some ParkA62Data.p47)=true := by decide +kernel

theorem step46_eq : ((compileChunked? 4741 ParkA62Data.p46).map (fun c => c.out))=
 some ParkA62Data.p47 := ParkAOptionBool.optionEq_sound _ _ step46_bool

theorem step47_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4742 ParkA62Data.p47).map (fun c => c.out))
 (some ParkA62Data.p48)=true := by decide +kernel

theorem step47_eq : ((compileChunked? 4742 ParkA62Data.p47).map (fun c => c.out))=
 some ParkA62Data.p48 := ParkAOptionBool.optionEq_sound _ _ step47_bool

theorem step48_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4743 ParkA62Data.p48).map (fun c => c.out))
 (some ParkA62Data.p49)=true := by decide +kernel

theorem step48_eq : ((compileChunked? 4743 ParkA62Data.p48).map (fun c => c.out))=
 some ParkA62Data.p49 := ParkAOptionBool.optionEq_sound _ _ step48_bool

theorem step49_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4744 ParkA62Data.p49).map (fun c => c.out))
 (some ParkA62Data.p50)=true := by decide +kernel

theorem step49_eq : ((compileChunked? 4744 ParkA62Data.p49).map (fun c => c.out))=
 some ParkA62Data.p50 := ParkAOptionBool.optionEq_sound _ _ step49_bool

theorem step50_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4745 ParkA62Data.p50).map (fun c => c.out))
 (some ParkA62Data.p51)=true := by decide +kernel

theorem step50_eq : ((compileChunked? 4745 ParkA62Data.p50).map (fun c => c.out))=
 some ParkA62Data.p51 := ParkAOptionBool.optionEq_sound _ _ step50_bool

theorem step51_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4746 ParkA62Data.p51).map (fun c => c.out))
 (some ParkA62Data.p52)=true := by decide +kernel

theorem step51_eq : ((compileChunked? 4746 ParkA62Data.p51).map (fun c => c.out))=
 some ParkA62Data.p52 := ParkAOptionBool.optionEq_sound _ _ step51_bool

theorem step52_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4747 ParkA62Data.p52).map (fun c => c.out))
 (some ParkA62Data.p53)=true := by decide +kernel

theorem step52_eq : ((compileChunked? 4747 ParkA62Data.p52).map (fun c => c.out))=
 some ParkA62Data.p53 := ParkAOptionBool.optionEq_sound _ _ step52_bool

theorem step53_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4748 ParkA62Data.p53).map (fun c => c.out))
 (some ParkA62Data.p54)=true := by decide +kernel

theorem step53_eq : ((compileChunked? 4748 ParkA62Data.p53).map (fun c => c.out))=
 some ParkA62Data.p54 := ParkAOptionBool.optionEq_sound _ _ step53_bool

theorem step54_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4749 ParkA62Data.p54).map (fun c => c.out))
 (some ParkA62Data.p55)=true := by decide +kernel

theorem step54_eq : ((compileChunked? 4749 ParkA62Data.p54).map (fun c => c.out))=
 some ParkA62Data.p55 := ParkAOptionBool.optionEq_sound _ _ step54_bool

theorem step55_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4750 ParkA62Data.p55).map (fun c => c.out))
 (some ParkA62Data.p56)=true := by decide +kernel

theorem step55_eq : ((compileChunked? 4750 ParkA62Data.p55).map (fun c => c.out))=
 some ParkA62Data.p56 := ParkAOptionBool.optionEq_sound _ _ step55_bool

theorem step56_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4751 ParkA62Data.p56).map (fun c => c.out))
 (some ParkA62Data.p57)=true := by decide +kernel

theorem step56_eq : ((compileChunked? 4751 ParkA62Data.p56).map (fun c => c.out))=
 some ParkA62Data.p57 := ParkAOptionBool.optionEq_sound _ _ step56_bool

theorem step57_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4752 ParkA62Data.p57).map (fun c => c.out))
 (some ParkA62Data.p58)=true := by decide +kernel

theorem step57_eq : ((compileChunked? 4752 ParkA62Data.p57).map (fun c => c.out))=
 some ParkA62Data.p58 := ParkAOptionBool.optionEq_sound _ _ step57_bool

theorem step58_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4753 ParkA62Data.p58).map (fun c => c.out))
 (some ParkA62Data.p59)=true := by decide +kernel

theorem step58_eq : ((compileChunked? 4753 ParkA62Data.p58).map (fun c => c.out))=
 some ParkA62Data.p59 := ParkAOptionBool.optionEq_sound _ _ step58_bool

theorem step59_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4754 ParkA62Data.p59).map (fun c => c.out))
 (some ParkA62Data.p60)=true := by decide +kernel

theorem step59_eq : ((compileChunked? 4754 ParkA62Data.p59).map (fun c => c.out))=
 some ParkA62Data.p60 := ParkAOptionBool.optionEq_sound _ _ step59_bool

theorem step60_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4755 ParkA62Data.p60).map (fun c => c.out))
 (some ParkA62Data.p61)=true := by decide +kernel

theorem step60_eq : ((compileChunked? 4755 ParkA62Data.p60).map (fun c => c.out))=
 some ParkA62Data.p61 := ParkAOptionBool.optionEq_sound _ _ step60_bool

theorem step61_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4756 ParkA62Data.p61).map (fun c => c.out))
 (some ParkA62Data.p62)=true := by decide +kernel

theorem step61_eq : ((compileChunked? 4756 ParkA62Data.p61).map (fun c => c.out))=
 some ParkA62Data.p62 := ParkAOptionBool.optionEq_sound _ _ step61_bool

theorem tail_chain : ParkAChain.Steps [4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkAData.p33 ParkA62Data.p62 :=
 ParkAChain.Steps.cons 4728 [4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkAData.p33 ParkA62Data.p34 ParkA62Data.p62 step33_eq
  (ParkAChain.Steps.cons 4729 [4730,4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p34 ParkA62Data.p35 ParkA62Data.p62 step34_eq
  (ParkAChain.Steps.cons 4730 [4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p35 ParkA62Data.p36 ParkA62Data.p62 step35_eq
  (ParkAChain.Steps.cons 4731 [4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p36 ParkA62Data.p37 ParkA62Data.p62 step36_eq
  (ParkAChain.Steps.cons 4732 [4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p37 ParkA62Data.p38 ParkA62Data.p62 step37_eq
  (ParkAChain.Steps.cons 4733 [4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p38 ParkA62Data.p39 ParkA62Data.p62 step38_eq
  (ParkAChain.Steps.cons 4734 [4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p39 ParkA62Data.p40 ParkA62Data.p62 step39_eq
  (ParkAChain.Steps.cons 4735 [4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p40 ParkA62Data.p41 ParkA62Data.p62 step40_eq
  (ParkAChain.Steps.cons 4736 [4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p41 ParkA62Data.p42 ParkA62Data.p62 step41_eq
  (ParkAChain.Steps.cons 4737 [4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p42 ParkA62Data.p43 ParkA62Data.p62 step42_eq
  (ParkAChain.Steps.cons 4738 [4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p43 ParkA62Data.p44 ParkA62Data.p62 step43_eq
  (ParkAChain.Steps.cons 4739 [4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p44 ParkA62Data.p45 ParkA62Data.p62 step44_eq
  (ParkAChain.Steps.cons 4740 [4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p45 ParkA62Data.p46 ParkA62Data.p62 step45_eq
  (ParkAChain.Steps.cons 4741 [4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p46 ParkA62Data.p47 ParkA62Data.p62 step46_eq
  (ParkAChain.Steps.cons 4742 [4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p47 ParkA62Data.p48 ParkA62Data.p62 step47_eq
  (ParkAChain.Steps.cons 4743 [4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p48 ParkA62Data.p49 ParkA62Data.p62 step48_eq
  (ParkAChain.Steps.cons 4744 [4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p49 ParkA62Data.p50 ParkA62Data.p62 step49_eq
  (ParkAChain.Steps.cons 4745 [4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p50 ParkA62Data.p51 ParkA62Data.p62 step50_eq
  (ParkAChain.Steps.cons 4746 [4747,4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p51 ParkA62Data.p52 ParkA62Data.p62 step51_eq
  (ParkAChain.Steps.cons 4747 [4748,4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p52 ParkA62Data.p53 ParkA62Data.p62 step52_eq
  (ParkAChain.Steps.cons 4748 [4749,4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p53 ParkA62Data.p54 ParkA62Data.p62 step53_eq
  (ParkAChain.Steps.cons 4749 [4750,4751,4752,4753,4754,4755,4756] ParkA62Data.p54 ParkA62Data.p55 ParkA62Data.p62 step54_eq
  (ParkAChain.Steps.cons 4750 [4751,4752,4753,4754,4755,4756] ParkA62Data.p55 ParkA62Data.p56 ParkA62Data.p62 step55_eq
  (ParkAChain.Steps.cons 4751 [4752,4753,4754,4755,4756] ParkA62Data.p56 ParkA62Data.p57 ParkA62Data.p62 step56_eq
  (ParkAChain.Steps.cons 4752 [4753,4754,4755,4756] ParkA62Data.p57 ParkA62Data.p58 ParkA62Data.p62 step57_eq
  (ParkAChain.Steps.cons 4753 [4754,4755,4756] ParkA62Data.p58 ParkA62Data.p59 ParkA62Data.p62 step58_eq
  (ParkAChain.Steps.cons 4754 [4755,4756] ParkA62Data.p59 ParkA62Data.p60 ParkA62Data.p62 step59_eq
  (ParkAChain.Steps.cons 4755 [4756] ParkA62Data.p60 ParkA62Data.p61 ParkA62Data.p62 step60_eq
  (ParkAChain.Steps.cons 4756 [] ParkA62Data.p61 ParkA62Data.p62 ParkA62Data.p62 step61_eq
  (ParkAChain.Steps.nil ParkA62Data.p62)))))))))))))))))))))))))))))

theorem chain62 : ParkAChain.Steps (ParkA62Many.loans Baselines.layout.dialogStreamedSquareWide)
 ParkAData.p0 ParkA62Data.p62 := by
 rw [hosts_eq,ParkAStagedProof.hosts_eq]
 exact append _ _ _ _ _ ParkAStagedProof.chain tail_chain

theorem compiled_outputs :
 (compileManyChunked? (ParkA62Many.loans Baselines.layout.dialogStreamedSquareWide)
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).map
  (fun c => c.out)=some ParkA62Data.p62 := by
 rw [←input_eq]
 exact ParkAChain.outputs _ _ _ chain62

theorem actual_compiled :
 (compileManyChunked? (ParkA62Many.loans Baselines.layout.dialogStreamedSquareWide)
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).isSome=true := by
 rw [←input_eq]
 exact ParkAChain.isSome _ _ _ chain62

#print axioms append
#print axioms input_eq
#print axioms hosts_eq
#print axioms tail_chain
#print axioms compiled_outputs
#print axioms actual_compiled
end ParkA62StagedProof
