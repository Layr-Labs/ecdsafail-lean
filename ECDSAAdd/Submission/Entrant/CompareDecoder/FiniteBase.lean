import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteBase
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
namespace ECDSAAdd.Entrant.CompareDecoder
open Arithmetic TerminalGraph DirectDecoder
def comparePolys : List Polynomial := [[[2], [3], [4], [12], [25], [1, 3], [1, 12], [1, 13], [1, 25], [2, 11], [3, 11], [3, 12], [3, 13], [3, 25], [12, 25], [13, 25]], [[3], [5], [3, 4], [3, 11], [3, 12], [3, 13], [3, 26], [4, 11], [4, 12], [4, 13], [4, 26], [12, 26], [13, 26]], [[4], [6], [17], [18], [27], [4, 11], [5, 11], [5, 16], [5, 27], [16, 27], [17, 27]], [[5], [6], [7], [28], [4, 6], [4, 28], [5, 11], [6, 11], [6, 28]], [[6], [7], [8], [12], [29], [5, 7], [5, 29], [6, 11], [7, 11], [7, 29]], [[7], [8], [9], [30], [6, 8], [6, 12], [6, 30], [7, 11], [8, 11], [8, 12], [8, 30], [12, 30]], [[8], [9], [10], [20], [21], [31], [7, 9], [7, 31], [8, 11], [9, 11], [9, 19], [9, 31], [11, 20], [11, 21], [12, 21], [19, 31]]]
def cmpSteps : List Bool → List Bool → Bool → List Bool
 | [],_,_=>[]
 | y::ys,k::ks,t=>let v:=if k then y && t else y || t;v::cmpSteps ys ks v
 | _,[],_=>[]
def seedIndex (x : Nat) : Nat :=
 (x.testBit 0).toNat+2*(x.testBit 10).toNat+4*(x.testBit 11).toNat+
 8*(x.testBit 12).toNat+16*(x.testBit 13).toNat+32*(x.testBit 14).toNat
def valid (x : Nat) : Bool := (2305880426972133179:Nat).testBit (seedIndex x)
def compareVars (x : Nat) : List Bool :=
 [true]++((List.range 10).map x.testBit)++
 [x.testBit 10,x.testBit 11,x.testBit 1 && x.testBit 11]++
 [x.testBit 14]++cmpSteps ((List.range 9).map (fun i=>x.testBit (i+1)))
 [true,false,true,false,true,true,true,true,true] (x.testBit 14)++(lowRs x).drop 4
end ECDSAAdd.Entrant.CompareDecoder
