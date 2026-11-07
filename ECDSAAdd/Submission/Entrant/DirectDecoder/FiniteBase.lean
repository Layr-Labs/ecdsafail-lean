import ECDSAAdd.Submission.Entrant.ExitMerge
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

abbrev Polynomial := List (List Nat)

def evalPoly (p : Polynomial) (v : List Bool) : Bool :=
 p.foldr (fun t z => (t.foldr (fun i z => v.getD i false && z) true) ^^ z) false

def chunk : List Bool → List Bool → Bool → Bool → Bool → Bool → List Bool
 | [],_,_,_,_,_=>[]
 | y::ys,d::ds,prev,sigma,a,c=>
   let raw:=prev ^^ y ^^ sigma ^^ a
   (raw ^^ d ^^ c)::chunk ys ds y sigma (carryBit prev (y ^^ sigma) a) (carryBit d raw c)
 | _::_,[],_,_,_,_=>[]

def seedOK (p s a c : Bool) : Bool :=
 (!s || ((a == !p) && !c)) && !(c && a && !p)

def lowPolys : List Polynomial := [[[1], [15]], [[1], [2], [16], [1, 14], [1, 15], [14, 16]], [[1], [2], [3], [21], [1, 14], [2, 14], [2, 16], [2, 21], [16, 21]], [[2], [3], [4], [22], [1, 3], [1, 22], [2, 14], [3, 14], [3, 22]], [[3], [4], [5], [15], [23], [2, 4], [2, 23], [3, 14], [4, 14], [4, 23]], [[4], [5], [6], [17], [24], [3, 5], [3, 15], [3, 24], [4, 14], [5, 14], [5, 24], [15, 24]], [[5], [6], [7], [15], [25], [4, 6], [4, 15], [4, 17], [4, 25], [5, 14], [6, 14], [6, 15], [6, 17], [6, 25], [15, 25], [17, 25]], [[6], [8], [18], [6, 14], [6, 15], [6, 17], [6, 26], [7, 14], [7, 15], [7, 17], [7, 26], [15, 26], [17, 26]], [[7], [8], [9], [27], [6, 8], [6, 27], [7, 14], [8, 14], [8, 18], [8, 27], [18, 27]], [[8], [9], [10], [28], [7, 9], [7, 28], [8, 14], [9, 14], [9, 28]], [[9], [10], [11], [15], [29], [8, 10], [8, 29], [9, 14], [10, 14], [10, 29]], [[10], [11], [12], [19], [30], [9, 11], [9, 30], [10, 14], [11, 14], [11, 15], [11, 30], [15, 30]], [[11], [12], [13], [31], [10, 12], [10, 19], [10, 31], [11, 14], [12, 14], [12, 19], [12, 31], [19, 31]]]

def highPolys : List Polynomial := [[[1], [5], [6], [8], [12], [5, 7], [5, 8], [5, 11], [6, 11], [7, 8]], [[1], [2], [5], [14], [15], [1, 6], [1, 11], [1, 15], [5, 11], [6, 12], [6, 15], [12, 15]], [[1], [2], [3], [16], [1, 11], [2, 5], [2, 11], [2, 12], [2, 14], [2, 16], [5, 12], [5, 14], [5, 16], [12, 16], [14, 16]], [[2], [4], [14], [2, 3], [2, 11], [2, 14], [2, 17], [3, 11], [3, 14], [3, 17], [14, 17]]]

def lowYs (x : Nat) : List Bool := [false,false,false]++(List.range 10).map x.testBit

def lowRs (x : Nat) : List Bool := [false,false,false,false]++
 chunk ((List.range 9).map (fun j=>x.testBit (j+1)))
   ((List.range 9).map (fun j=>x.testBit 11 && (977:Nat).testBit (j+4)))
   (x.testBit 0) (x.testBit 10) (x.testBit 12) (x.testBit 13)

def lowVars (x : Nat) : List Bool := [true]++lowYs x++[x.testBit 10,x.testBit 11,false]++
 [x.testBit 1 && x.testBit 11,x.testBit 2 && x.testBit 3,x.testBit 5 && x.testBit 11]++lowRs x

def lowValid (x : Nat) : Bool :=
 !(x.testBit 10 && x.testBit 11) && seedOK (x.testBit 0) (x.testBit 10) (x.testBit 12) (x.testBit 13) &&
 !(x.testBit 12 && x.testBit 13 && !(x.testBit 11))

def highRs (x : Nat) : List Bool := chunk ((List.range 6).map (fun j=>x.testBit (j+1)))
 [false,false,x.testBit 8,false,false,false] (x.testBit 0) (x.testBit 7) (x.testBit 9) (x.testBit 10)

def highVars (x : Nat) : List Bool :=
 [true,x.testBit 3,x.testBit 4,x.testBit 5,x.testBit 6,x.testBit 2,x.testBit 1,x.testBit 0,
 (highRs x).getD 1 false,(highRs x).getD 0 false,false,x.testBit 7,x.testBit 8,false,
 x.testBit 3 && x.testBit 8]++(highRs x).drop 2

def highValid (x : Nat) : Bool :=
 !(x.testBit 7 && x.testBit 8) && seedOK (x.testBit 0) (x.testBit 7) (x.testBit 9) (x.testBit 10) &&
 !(x.testBit 9 && x.testBit 10 && !(x.testBit 8))

def initialRs (x : Nat) : List Bool := chunk ((List.range 6).map x.testBit)
 [x.testBit 7,x.testBit 8 && !(x.testBit 6),false,false,x.testBit 7,false]
 false (x.testBit 6) (x.testBit 6) false

def initialVars (x : Nat) : List Bool := [true]++((List.range 13).map (fun j=>if j<6 then x.testBit j else false))++
 [x.testBit 6,x.testBit 7,x.testBit 8,x.testBit 4 && x.testBit 7,false,false]++initialRs x

end ECDSAAdd.Entrant.DirectDecoder
