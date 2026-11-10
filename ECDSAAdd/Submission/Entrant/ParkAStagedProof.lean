import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAData

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ParkAStagedProof
                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                              
                                                            
                                               

                   
                                                                                  
                                               

                                                                                                                                                                                                                                     
                                                                                                                                                                                                                                               
                                                                                                                                                                                                                                            
                                                                                                                                                                                                                                       
                                                                                                                                                                                                                                  
                                                                                                                                                                                                                             
                                                                                                                                                                                                                        
                                                                                                                                                                                                                   
                                                                                                                                                                                                              
                                                                                                                                                                                                         
                                                                                                                                                                                                     
                                                                                                                                                                                                 
                                                                                                                                                                                            
                                                                                                                                                                                       
                                                                                                                                                                                  
                                                                                                                                                                             
                                                                                                                                                                        
                                                                                                                                                                   
                                                                                                                                                              
                                                                                                                                                         
                                                                                                                                                    
                                                                                                                                               
                                                                                                                                          
                                                                                                                                     
                                                                                                                                
                                                                                                                           
                                                                                                                      
                                                                                                                 
                                                                                                            
                                                                                                       
                                                                                                  
                                                                                             
                                                                                        
                                                                                    
                                                                      

                          
                                                                                             
              
                                     

                         
                                 
                                                                                                      
                
                                                               
              
            

#print axioms input_eq
                      
                   
                              
                             
end ParkAStagedProof

end

section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.BThreeStaged301
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open ControlLoan1589BFFold ZeroReadDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop
/-- Proof-local constructor replacement, with the original old compiler unchanged. -/
def coreFast (L : CuccaroStreamedSquareWideLayout) : Program :=
  kw L ++ (ParkAInputFast.qprogFast (rotWCore L) SquareReduction.p ++ kw L)

theorem coreFast_eq (L : CuccaroStreamedSquareWideLayout) : coreFast L = wCoreK L := by
  simp only [coreFast, ParkAInputFast.qprogFast_eq, wCoreK, wCoreTq]

def middleFast (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 prepare4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) ++
 ((wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) ++ (coreFast L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0))) ++
 finish4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L))

/-- Exact ordered Program syntax for arbitrary layouts and controls; not just isSome equality. -/
theorem middleFast_eq (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
    middleFast L c = LowBitCarryDevelop.wMidFullCCC0 L c := by
  simp only [middleFast, coreFast_eq, LowBitCarryDevelop.wMidFullCCC0]


def L : CuccaroStreamedSquareWideLayout := Baselines.layout.dialogStreamedSquareWide
def c : Wire := Baselines.layout.core.generic
theorem input_bool : ParkAProgramBool.programEq BData301.p0 (middleFast L c)=true := by decide +kernel
theorem input_fast_eq : BData301.p0 = middleFast L c := ParkAProgramBool.programEq_sound _ _ input_bool
theorem input_eq : BData301.p0 = LowBitCarryDevelop.wMidFullCCC0 L c := input_fast_eq.trans (middleFast_eq L c)

                                                                                                                                                    
                                                                                                                                            

                                                                                                                                                    
                                                                                                                                            

                                                                                                                                                    
                                                                                                                                            

                                                                            
                                                                                                 
                                                                           
                                                                                               
                                                                                                                     
                                                                      
/-- Only literal input membership is evaluated here; the whole B body is never constructed. -/
theorem data_uses_r : FourthASavedCarryDevelop.hasWire BData301.p0 4672=true := by decide +kernel
                                                                                                 
                                                                                                 
end ECDSAAdd.Entrant.BThreeStaged301

section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.BManySteps
open ECDSAAdd ZeroReadDevelop

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                    

                                                                                                                                            

                                                                                                                                                     

                                                                                                                                             

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                       

                                                                                                                                                

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     


end ECDSAAdd.Entrant.BManySteps

end

end

section
open ECDSAAdd ECDSAAdd.Entrant ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
                                      
                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                       

                                                                                                                                               


                                
end
