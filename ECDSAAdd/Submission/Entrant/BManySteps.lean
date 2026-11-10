import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAChain
import ECDSAAdd.Submission.Entrant.BManyData
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.BManySteps
open ECDSAAdd ZeroReadDevelop

theorem step0_bool : ParkAOptionBool.optionEq ((compileChunked? 4674 BManyData.p0).map (fun c=>c.out)) (some BManyData.p1)=true := by decide +kernel

theorem step0_eq : (compileChunked? 4674 BManyData.p0).map (fun c=>c.out)=some BManyData.p1 := ParkAOptionBool.optionEq_sound _ _ step0_bool

theorem step1_bool : ParkAOptionBool.optionEq ((compileChunked? 4675 BManyData.p1).map (fun c=>c.out)) (some BManyData.p2)=true := by decide +kernel

theorem step1_eq : (compileChunked? 4675 BManyData.p1).map (fun c=>c.out)=some BManyData.p2 := ParkAOptionBool.optionEq_sound _ _ step1_bool

theorem step2_bool : ParkAOptionBool.optionEq ((compileChunked? 4676 BManyData.p2).map (fun c=>c.out)) (some BManyData.p3)=true := by decide +kernel

theorem step2_eq : (compileChunked? 4676 BManyData.p2).map (fun c=>c.out)=some BManyData.p3 := ParkAOptionBool.optionEq_sound _ _ step2_bool

theorem step3_bool : ParkAOptionBool.optionEq ((compileChunked? 4677 BManyData.p3).map (fun c=>c.out)) (some BManyData.p4)=true := by decide +kernel

theorem step3_eq : (compileChunked? 4677 BManyData.p3).map (fun c=>c.out)=some BManyData.p4 := ParkAOptionBool.optionEq_sound _ _ step3_bool

theorem step4_bool : ParkAOptionBool.optionEq ((compileChunked? 4678 BManyData.p4).map (fun c=>c.out)) (some BManyData.p5)=true := by decide +kernel

theorem step4_eq : (compileChunked? 4678 BManyData.p4).map (fun c=>c.out)=some BManyData.p5 := ParkAOptionBool.optionEq_sound _ _ step4_bool

theorem step5_bool : ParkAOptionBool.optionEq ((compileChunked? 4679 BManyData.p5).map (fun c=>c.out)) (some BManyData.p6)=true := by decide +kernel

theorem step5_eq : (compileChunked? 4679 BManyData.p5).map (fun c=>c.out)=some BManyData.p6 := ParkAOptionBool.optionEq_sound _ _ step5_bool

theorem step6_bool : ParkAOptionBool.optionEq ((compileChunked? 4680 BManyData.p6).map (fun c=>c.out)) (some BManyData.p7)=true := by decide +kernel

theorem step6_eq : (compileChunked? 4680 BManyData.p6).map (fun c=>c.out)=some BManyData.p7 := ParkAOptionBool.optionEq_sound _ _ step6_bool

theorem step7_bool : ParkAOptionBool.optionEq ((compileChunked? 4681 BManyData.p7).map (fun c=>c.out)) (some BManyData.p8)=true := by decide +kernel

theorem step7_eq : (compileChunked? 4681 BManyData.p7).map (fun c=>c.out)=some BManyData.p8 := ParkAOptionBool.optionEq_sound _ _ step7_bool

theorem step8_bool : ParkAOptionBool.optionEq ((compileChunked? 4682 BManyData.p8).map (fun c=>c.out)) (some BManyData.p9)=true := by decide +kernel

theorem step8_eq : (compileChunked? 4682 BManyData.p8).map (fun c=>c.out)=some BManyData.p9 := ParkAOptionBool.optionEq_sound _ _ step8_bool

theorem step9_bool : ParkAOptionBool.optionEq ((compileChunked? 4683 BManyData.p9).map (fun c=>c.out)) (some BManyData.p10)=true := by decide +kernel

theorem step9_eq : (compileChunked? 4683 BManyData.p9).map (fun c=>c.out)=some BManyData.p10 := ParkAOptionBool.optionEq_sound _ _ step9_bool

theorem step10_bool : ParkAOptionBool.optionEq ((compileChunked? 4684 BManyData.p10).map (fun c=>c.out)) (some BManyData.p11)=true := by decide +kernel

theorem step10_eq : (compileChunked? 4684 BManyData.p10).map (fun c=>c.out)=some BManyData.p11 := ParkAOptionBool.optionEq_sound _ _ step10_bool

theorem step11_bool : ParkAOptionBool.optionEq ((compileChunked? 4685 BManyData.p11).map (fun c=>c.out)) (some BManyData.p12)=true := by decide +kernel

theorem step11_eq : (compileChunked? 4685 BManyData.p11).map (fun c=>c.out)=some BManyData.p12 := ParkAOptionBool.optionEq_sound _ _ step11_bool

theorem step12_bool : ParkAOptionBool.optionEq ((compileChunked? 4686 BManyData.p12).map (fun c=>c.out)) (some BManyData.p13)=true := by decide +kernel

theorem step12_eq : (compileChunked? 4686 BManyData.p12).map (fun c=>c.out)=some BManyData.p13 := ParkAOptionBool.optionEq_sound _ _ step12_bool

theorem step13_bool : ParkAOptionBool.optionEq ((compileChunked? 4687 BManyData.p13).map (fun c=>c.out)) (some BManyData.p14)=true := by decide +kernel

theorem step13_eq : (compileChunked? 4687 BManyData.p13).map (fun c=>c.out)=some BManyData.p14 := ParkAOptionBool.optionEq_sound _ _ step13_bool

theorem step14_bool : ParkAOptionBool.optionEq ((compileChunked? 4688 BManyData.p14).map (fun c=>c.out)) (some BManyData.p15)=true := by decide +kernel

theorem step14_eq : (compileChunked? 4688 BManyData.p14).map (fun c=>c.out)=some BManyData.p15 := ParkAOptionBool.optionEq_sound _ _ step14_bool

theorem step15_bool : ParkAOptionBool.optionEq ((compileChunked? 4689 BManyData.p15).map (fun c=>c.out)) (some BManyData.p16)=true := by decide +kernel

theorem step15_eq : (compileChunked? 4689 BManyData.p15).map (fun c=>c.out)=some BManyData.p16 := ParkAOptionBool.optionEq_sound _ _ step15_bool

theorem step16_bool : ParkAOptionBool.optionEq ((compileChunked? 4690 BManyData.p16).map (fun c=>c.out)) (some BManyData.p17)=true := by decide +kernel

theorem step16_eq : (compileChunked? 4690 BManyData.p16).map (fun c=>c.out)=some BManyData.p17 := ParkAOptionBool.optionEq_sound _ _ step16_bool

theorem step17_bool : ParkAOptionBool.optionEq ((compileChunked? 4691 BManyData.p17).map (fun c=>c.out)) (some BManyData.p18)=true := by decide +kernel

theorem step17_eq : (compileChunked? 4691 BManyData.p17).map (fun c=>c.out)=some BManyData.p18 := ParkAOptionBool.optionEq_sound _ _ step17_bool

theorem step18_bool : ParkAOptionBool.optionEq ((compileChunked? 4692 BManyData.p18).map (fun c=>c.out)) (some BManyData.p19)=true := by decide +kernel

theorem step18_eq : (compileChunked? 4692 BManyData.p18).map (fun c=>c.out)=some BManyData.p19 := ParkAOptionBool.optionEq_sound _ _ step18_bool

theorem step19_bool : ParkAOptionBool.optionEq ((compileChunked? 4694 BManyData.p19).map (fun c=>c.out)) (some BManyData.p20)=true := by decide +kernel

theorem step19_eq : (compileChunked? 4694 BManyData.p19).map (fun c=>c.out)=some BManyData.p20 := ParkAOptionBool.optionEq_sound _ _ step19_bool

theorem step20_bool : ParkAOptionBool.optionEq ((compileChunked? 4695 BManyData.p20).map (fun c=>c.out)) (some BManyData.p21)=true := by decide +kernel

theorem step20_eq : (compileChunked? 4695 BManyData.p20).map (fun c=>c.out)=some BManyData.p21 := ParkAOptionBool.optionEq_sound _ _ step20_bool

theorem step21_bool : ParkAOptionBool.optionEq ((compileChunked? 4696 BManyData.p21).map (fun c=>c.out)) (some BManyData.p22)=true := by decide +kernel

theorem step21_eq : (compileChunked? 4696 BManyData.p21).map (fun c=>c.out)=some BManyData.p22 := ParkAOptionBool.optionEq_sound _ _ step21_bool

theorem chain : ParkAChain.Steps [4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4694,4695,4696] BManyData.p0 BManyData.p22 := .cons 4674 _ _ _ _ step0_eq (.cons 4675 _ _ _ _ step1_eq (.cons 4676 _ _ _ _ step2_eq (.cons 4677 _ _ _ _ step3_eq (.cons 4678 _ _ _ _ step4_eq (.cons 4679 _ _ _ _ step5_eq (.cons 4680 _ _ _ _ step6_eq (.cons 4681 _ _ _ _ step7_eq (.cons 4682 _ _ _ _ step8_eq (.cons 4683 _ _ _ _ step9_eq (.cons 4684 _ _ _ _ step10_eq (.cons 4685 _ _ _ _ step11_eq (.cons 4686 _ _ _ _ step12_eq (.cons 4687 _ _ _ _ step13_eq (.cons 4688 _ _ _ _ step14_eq (.cons 4689 _ _ _ _ step15_eq (.cons 4690 _ _ _ _ step16_eq (.cons 4691 _ _ _ _ step17_eq (.cons 4692 _ _ _ _ step18_eq (.cons 4694 _ _ _ _ step19_eq (.cons 4695 _ _ _ _ step20_eq (.cons 4696 _ _ _ _ step21_eq (.nil _))))))))))))))))))))))


end ECDSAAdd.Entrant.BManySteps
