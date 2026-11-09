import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAData
import ECDSAAdd.Submission.Entrant.ParkAProgramBool
import ECDSAAdd.Submission.Entrant.ParkAChain
import ECDSAAdd.Submission.Entrant.ParkAInputFast
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ParkAStagedProof

theorem input_bool : ParkAProgramBool.programEq ParkAData.p0
 (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)=true := by
 exact (ParkAProgramBool.programEq_iff _ _).mpr ParkAInputFast.original_input_eq

theorem input_eq : ParkAData.p0 =
 aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic :=
 ParkAProgramBool.programEq_sound _ _ input_bool

def actualHosts : List Wire :=
 (Baselines.layout.dialogStreamedSquareWide.core.work.drop 163).take 33

theorem hosts_eq : actualHosts = [4664,4665,4666,4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] := by decide +kernel

theorem step00_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4664 ParkAData.p0).map (fun c => c.out))
 (some ParkAData.p1)=true := by decide +kernel

theorem step00_eq :
 ((compileChunked? 4664 ParkAData.p0).map (fun c => c.out))=some ParkAData.p1 :=
 ParkAOptionBool.optionEq_sound _ _ step00_bool

theorem step01_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4665 ParkAData.p1).map (fun c => c.out))
 (some ParkAData.p2)=true := by decide +kernel

theorem step01_eq :
 ((compileChunked? 4665 ParkAData.p1).map (fun c => c.out))=some ParkAData.p2 :=
 ParkAOptionBool.optionEq_sound _ _ step01_bool

theorem step02_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4666 ParkAData.p2).map (fun c => c.out))
 (some ParkAData.p3)=true := by decide +kernel

theorem step02_eq :
 ((compileChunked? 4666 ParkAData.p2).map (fun c => c.out))=some ParkAData.p3 :=
 ParkAOptionBool.optionEq_sound _ _ step02_bool

theorem step03_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4667 ParkAData.p3).map (fun c => c.out))
 (some ParkAData.p4)=true := by decide +kernel

theorem step03_eq :
 ((compileChunked? 4667 ParkAData.p3).map (fun c => c.out))=some ParkAData.p4 :=
 ParkAOptionBool.optionEq_sound _ _ step03_bool

theorem step04_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4668 ParkAData.p4).map (fun c => c.out))
 (some ParkAData.p5)=true := by decide +kernel

theorem step04_eq :
 ((compileChunked? 4668 ParkAData.p4).map (fun c => c.out))=some ParkAData.p5 :=
 ParkAOptionBool.optionEq_sound _ _ step04_bool

theorem step05_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4669 ParkAData.p5).map (fun c => c.out))
 (some ParkAData.p6)=true := by decide +kernel

theorem step05_eq :
 ((compileChunked? 4669 ParkAData.p5).map (fun c => c.out))=some ParkAData.p6 :=
 ParkAOptionBool.optionEq_sound _ _ step05_bool

theorem step06_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4670 ParkAData.p6).map (fun c => c.out))
 (some ParkAData.p7)=true := by decide +kernel

theorem step06_eq :
 ((compileChunked? 4670 ParkAData.p6).map (fun c => c.out))=some ParkAData.p7 :=
 ParkAOptionBool.optionEq_sound _ _ step06_bool

theorem step07_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4671 ParkAData.p7).map (fun c => c.out))
 (some ParkAData.p8)=true := by decide +kernel

theorem step07_eq :
 ((compileChunked? 4671 ParkAData.p7).map (fun c => c.out))=some ParkAData.p8 :=
 ParkAOptionBool.optionEq_sound _ _ step07_bool

theorem step08_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4672 ParkAData.p8).map (fun c => c.out))
 (some ParkAData.p9)=true := by decide +kernel

theorem step08_eq :
 ((compileChunked? 4672 ParkAData.p8).map (fun c => c.out))=some ParkAData.p9 :=
 ParkAOptionBool.optionEq_sound _ _ step08_bool

theorem step09_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4673 ParkAData.p9).map (fun c => c.out))
 (some ParkAData.p10)=true := by decide +kernel

theorem step09_eq :
 ((compileChunked? 4673 ParkAData.p9).map (fun c => c.out))=some ParkAData.p10 :=
 ParkAOptionBool.optionEq_sound _ _ step09_bool

theorem step10_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4674 ParkAData.p10).map (fun c => c.out))
 (some ParkAData.p11)=true := by decide +kernel

theorem step10_eq :
 ((compileChunked? 4674 ParkAData.p10).map (fun c => c.out))=some ParkAData.p11 :=
 ParkAOptionBool.optionEq_sound _ _ step10_bool

theorem step11_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4675 ParkAData.p11).map (fun c => c.out))
 (some ParkAData.p12)=true := by decide +kernel

theorem step11_eq :
 ((compileChunked? 4675 ParkAData.p11).map (fun c => c.out))=some ParkAData.p12 :=
 ParkAOptionBool.optionEq_sound _ _ step11_bool

theorem step12_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4676 ParkAData.p12).map (fun c => c.out))
 (some ParkAData.p13)=true := by decide +kernel

theorem step12_eq :
 ((compileChunked? 4676 ParkAData.p12).map (fun c => c.out))=some ParkAData.p13 :=
 ParkAOptionBool.optionEq_sound _ _ step12_bool

theorem step13_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4677 ParkAData.p13).map (fun c => c.out))
 (some ParkAData.p14)=true := by decide +kernel

theorem step13_eq :
 ((compileChunked? 4677 ParkAData.p13).map (fun c => c.out))=some ParkAData.p14 :=
 ParkAOptionBool.optionEq_sound _ _ step13_bool

theorem step14_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4678 ParkAData.p14).map (fun c => c.out))
 (some ParkAData.p15)=true := by decide +kernel

theorem step14_eq :
 ((compileChunked? 4678 ParkAData.p14).map (fun c => c.out))=some ParkAData.p15 :=
 ParkAOptionBool.optionEq_sound _ _ step14_bool

theorem step15_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4679 ParkAData.p15).map (fun c => c.out))
 (some ParkAData.p16)=true := by decide +kernel

theorem step15_eq :
 ((compileChunked? 4679 ParkAData.p15).map (fun c => c.out))=some ParkAData.p16 :=
 ParkAOptionBool.optionEq_sound _ _ step15_bool

theorem step16_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4680 ParkAData.p16).map (fun c => c.out))
 (some ParkAData.p17)=true := by decide +kernel

theorem step16_eq :
 ((compileChunked? 4680 ParkAData.p16).map (fun c => c.out))=some ParkAData.p17 :=
 ParkAOptionBool.optionEq_sound _ _ step16_bool

theorem step17_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4681 ParkAData.p17).map (fun c => c.out))
 (some ParkAData.p18)=true := by decide +kernel

theorem step17_eq :
 ((compileChunked? 4681 ParkAData.p17).map (fun c => c.out))=some ParkAData.p18 :=
 ParkAOptionBool.optionEq_sound _ _ step17_bool

theorem step18_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4682 ParkAData.p18).map (fun c => c.out))
 (some ParkAData.p19)=true := by decide +kernel

theorem step18_eq :
 ((compileChunked? 4682 ParkAData.p18).map (fun c => c.out))=some ParkAData.p19 :=
 ParkAOptionBool.optionEq_sound _ _ step18_bool

theorem step19_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4683 ParkAData.p19).map (fun c => c.out))
 (some ParkAData.p20)=true := by decide +kernel

theorem step19_eq :
 ((compileChunked? 4683 ParkAData.p19).map (fun c => c.out))=some ParkAData.p20 :=
 ParkAOptionBool.optionEq_sound _ _ step19_bool

theorem step20_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4684 ParkAData.p20).map (fun c => c.out))
 (some ParkAData.p21)=true := by decide +kernel

theorem step20_eq :
 ((compileChunked? 4684 ParkAData.p20).map (fun c => c.out))=some ParkAData.p21 :=
 ParkAOptionBool.optionEq_sound _ _ step20_bool

theorem step21_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4685 ParkAData.p21).map (fun c => c.out))
 (some ParkAData.p22)=true := by decide +kernel

theorem step21_eq :
 ((compileChunked? 4685 ParkAData.p21).map (fun c => c.out))=some ParkAData.p22 :=
 ParkAOptionBool.optionEq_sound _ _ step21_bool

theorem step22_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4686 ParkAData.p22).map (fun c => c.out))
 (some ParkAData.p23)=true := by decide +kernel

theorem step22_eq :
 ((compileChunked? 4686 ParkAData.p22).map (fun c => c.out))=some ParkAData.p23 :=
 ParkAOptionBool.optionEq_sound _ _ step22_bool

theorem step23_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4687 ParkAData.p23).map (fun c => c.out))
 (some ParkAData.p24)=true := by decide +kernel

theorem step23_eq :
 ((compileChunked? 4687 ParkAData.p23).map (fun c => c.out))=some ParkAData.p24 :=
 ParkAOptionBool.optionEq_sound _ _ step23_bool

theorem step24_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4688 ParkAData.p24).map (fun c => c.out))
 (some ParkAData.p25)=true := by decide +kernel

theorem step24_eq :
 ((compileChunked? 4688 ParkAData.p24).map (fun c => c.out))=some ParkAData.p25 :=
 ParkAOptionBool.optionEq_sound _ _ step24_bool

theorem step25_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4689 ParkAData.p25).map (fun c => c.out))
 (some ParkAData.p26)=true := by decide +kernel

theorem step25_eq :
 ((compileChunked? 4689 ParkAData.p25).map (fun c => c.out))=some ParkAData.p26 :=
 ParkAOptionBool.optionEq_sound _ _ step25_bool

theorem step26_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4690 ParkAData.p26).map (fun c => c.out))
 (some ParkAData.p27)=true := by decide +kernel

theorem step26_eq :
 ((compileChunked? 4690 ParkAData.p26).map (fun c => c.out))=some ParkAData.p27 :=
 ParkAOptionBool.optionEq_sound _ _ step26_bool

theorem step27_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4691 ParkAData.p27).map (fun c => c.out))
 (some ParkAData.p28)=true := by decide +kernel

theorem step27_eq :
 ((compileChunked? 4691 ParkAData.p27).map (fun c => c.out))=some ParkAData.p28 :=
 ParkAOptionBool.optionEq_sound _ _ step27_bool

theorem step28_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4692 ParkAData.p28).map (fun c => c.out))
 (some ParkAData.p29)=true := by decide +kernel

theorem step28_eq :
 ((compileChunked? 4692 ParkAData.p28).map (fun c => c.out))=some ParkAData.p29 :=
 ParkAOptionBool.optionEq_sound _ _ step28_bool

theorem step29_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4693 ParkAData.p29).map (fun c => c.out))
 (some ParkAData.p30)=true := by decide +kernel

theorem step29_eq :
 ((compileChunked? 4693 ParkAData.p29).map (fun c => c.out))=some ParkAData.p30 :=
 ParkAOptionBool.optionEq_sound _ _ step29_bool

theorem step30_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4694 ParkAData.p30).map (fun c => c.out))
 (some ParkAData.p31)=true := by decide +kernel

theorem step30_eq :
 ((compileChunked? 4694 ParkAData.p30).map (fun c => c.out))=some ParkAData.p31 :=
 ParkAOptionBool.optionEq_sound _ _ step30_bool

theorem step31_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4695 ParkAData.p31).map (fun c => c.out))
 (some ParkAData.p32)=true := by decide +kernel

theorem step31_eq :
 ((compileChunked? 4695 ParkAData.p31).map (fun c => c.out))=some ParkAData.p32 :=
 ParkAOptionBool.optionEq_sound _ _ step31_bool

theorem step32_bool : ParkAOptionBool.optionEq
 ((compileChunked? 4696 ParkAData.p32).map (fun c => c.out))
 (some ParkAData.p33)=true := by decide +kernel

theorem step32_eq :
 ((compileChunked? 4696 ParkAData.p32).map (fun c => c.out))=some ParkAData.p33 :=
 ParkAOptionBool.optionEq_sound _ _ step32_bool

theorem chain : ParkAChain.Steps [4664,4665,4666,4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p0 ParkAData.p33 :=
 ParkAChain.Steps.cons 4664 [4665,4666,4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p0 ParkAData.p1 ParkAData.p33 step00_eq
  (ParkAChain.Steps.cons 4665 [4666,4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p1 ParkAData.p2 ParkAData.p33 step01_eq
  (ParkAChain.Steps.cons 4666 [4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p2 ParkAData.p3 ParkAData.p33 step02_eq
  (ParkAChain.Steps.cons 4667 [4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p3 ParkAData.p4 ParkAData.p33 step03_eq
  (ParkAChain.Steps.cons 4668 [4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p4 ParkAData.p5 ParkAData.p33 step04_eq
  (ParkAChain.Steps.cons 4669 [4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p5 ParkAData.p6 ParkAData.p33 step05_eq
  (ParkAChain.Steps.cons 4670 [4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p6 ParkAData.p7 ParkAData.p33 step06_eq
  (ParkAChain.Steps.cons 4671 [4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p7 ParkAData.p8 ParkAData.p33 step07_eq
  (ParkAChain.Steps.cons 4672 [4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p8 ParkAData.p9 ParkAData.p33 step08_eq
  (ParkAChain.Steps.cons 4673 [4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p9 ParkAData.p10 ParkAData.p33 step09_eq
  (ParkAChain.Steps.cons 4674 [4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p10 ParkAData.p11 ParkAData.p33 step10_eq
  (ParkAChain.Steps.cons 4675 [4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p11 ParkAData.p12 ParkAData.p33 step11_eq
  (ParkAChain.Steps.cons 4676 [4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p12 ParkAData.p13 ParkAData.p33 step12_eq
  (ParkAChain.Steps.cons 4677 [4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p13 ParkAData.p14 ParkAData.p33 step13_eq
  (ParkAChain.Steps.cons 4678 [4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p14 ParkAData.p15 ParkAData.p33 step14_eq
  (ParkAChain.Steps.cons 4679 [4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p15 ParkAData.p16 ParkAData.p33 step15_eq
  (ParkAChain.Steps.cons 4680 [4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p16 ParkAData.p17 ParkAData.p33 step16_eq
  (ParkAChain.Steps.cons 4681 [4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p17 ParkAData.p18 ParkAData.p33 step17_eq
  (ParkAChain.Steps.cons 4682 [4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p18 ParkAData.p19 ParkAData.p33 step18_eq
  (ParkAChain.Steps.cons 4683 [4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p19 ParkAData.p20 ParkAData.p33 step19_eq
  (ParkAChain.Steps.cons 4684 [4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p20 ParkAData.p21 ParkAData.p33 step20_eq
  (ParkAChain.Steps.cons 4685 [4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p21 ParkAData.p22 ParkAData.p33 step21_eq
  (ParkAChain.Steps.cons 4686 [4687,4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p22 ParkAData.p23 ParkAData.p33 step22_eq
  (ParkAChain.Steps.cons 4687 [4688,4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p23 ParkAData.p24 ParkAData.p33 step23_eq
  (ParkAChain.Steps.cons 4688 [4689,4690,4691,4692,4693,4694,4695,4696] ParkAData.p24 ParkAData.p25 ParkAData.p33 step24_eq
  (ParkAChain.Steps.cons 4689 [4690,4691,4692,4693,4694,4695,4696] ParkAData.p25 ParkAData.p26 ParkAData.p33 step25_eq
  (ParkAChain.Steps.cons 4690 [4691,4692,4693,4694,4695,4696] ParkAData.p26 ParkAData.p27 ParkAData.p33 step26_eq
  (ParkAChain.Steps.cons 4691 [4692,4693,4694,4695,4696] ParkAData.p27 ParkAData.p28 ParkAData.p33 step27_eq
  (ParkAChain.Steps.cons 4692 [4693,4694,4695,4696] ParkAData.p28 ParkAData.p29 ParkAData.p33 step28_eq
  (ParkAChain.Steps.cons 4693 [4694,4695,4696] ParkAData.p29 ParkAData.p30 ParkAData.p33 step29_eq
  (ParkAChain.Steps.cons 4694 [4695,4696] ParkAData.p30 ParkAData.p31 ParkAData.p33 step30_eq
  (ParkAChain.Steps.cons 4695 [4696] ParkAData.p31 ParkAData.p32 ParkAData.p33 step31_eq
  (ParkAChain.Steps.cons 4696 [] ParkAData.p32 ParkAData.p33 ParkAData.p33 step32_eq
  (ParkAChain.Steps.nil ParkAData.p33)))))))))))))))))))))))))))))))))

theorem compiled_outputs :
 (compileManyChunked? actualHosts ParkAData.p0).map (fun c => c.out)=some ParkAData.p33 := by
 rw [hosts_eq]
 exact ParkAChain.outputs _ _ _ chain

theorem actual_compiled :
 (compileManyChunked? actualHosts
  (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)).isSome=true := by
 rw [← input_eq]
 apply ParkAChain.isSome actualHosts ParkAData.p0 ParkAData.p33
 rw [hosts_eq]
 exact chain

#print axioms input_eq
#print axioms hosts_eq
#print axioms chain
#print axioms compiled_outputs
#print axioms actual_compiled
end ParkAStagedProof
