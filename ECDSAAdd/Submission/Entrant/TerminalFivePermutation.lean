import ECDSAAdd.Submission.Entrant.TerminalFiveDomain

namespace ECDSAAdd.Entrant.TerminalFivePermutation
open ECDSAAdd
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def port (q : Wire) : Wire :=
 if q<40 then TerminalFiveDomain.sites[q]!
 else if q=521 then 0
 else if q=522 then 1
 else if q=523 then 2
 else if q=524 then 3
 else if q=525 then 4
 else if q=526 then 5
 else if q=527 then 6
 else if q=528 then 7
 else if q=529 then 8
 else if q=530 then 9
 else if q=786 then 10
 else if q=787 then 11
 else if q=788 then 12
 else if q=789 then 13
 else if q=790 then 14
 else if q=791 then 15
 else if q=792 then 16
 else if q=793 then 17
 else if q=794 then 18
 else if q=795 then 19
 else if q=796 then 20
 else if q=797 then 21
 else if q=798 then 22
 else if q=799 then 23
 else if q=800 then 24
 else if q=801 then 25
 else if q=802 then 26
 else if q=803 then 27
 else if q=804 then 28
 else if q=805 then 29
 else if q=1550 then 30
 else if q=1551 then 31
 else if q=1552 then 32
 else if q=1553 then 33
 else if q=1554 then 34
 else if q=1556 then 35
 else if q=1557 then 36
 else if q=1558 then 37
 else if q=1559 then 38
 else if q=1560 then 39
 else q

theorem twice (q : Wire) : port (port q)=q := by
  by_cases low : q<40
  · change q<40 at low
    interval_cases q <;> decide +kernel
  by_cases e0 : q=521
  · subst q; decide +kernel
  by_cases e1 : q=522
  · subst q; decide +kernel
  by_cases e2 : q=523
  · subst q; decide +kernel
  by_cases e3 : q=524
  · subst q; decide +kernel
  by_cases e4 : q=525
  · subst q; decide +kernel
  by_cases e5 : q=526
  · subst q; decide +kernel
  by_cases e6 : q=527
  · subst q; decide +kernel
  by_cases e7 : q=528
  · subst q; decide +kernel
  by_cases e8 : q=529
  · subst q; decide +kernel
  by_cases e9 : q=530
  · subst q; decide +kernel
  by_cases e10 : q=786
  · subst q; decide +kernel
  by_cases e11 : q=787
  · subst q; decide +kernel
  by_cases e12 : q=788
  · subst q; decide +kernel
  by_cases e13 : q=789
  · subst q; decide +kernel
  by_cases e14 : q=790
  · subst q; decide +kernel
  by_cases e15 : q=791
  · subst q; decide +kernel
  by_cases e16 : q=792
  · subst q; decide +kernel
  by_cases e17 : q=793
  · subst q; decide +kernel
  by_cases e18 : q=794
  · subst q; decide +kernel
  by_cases e19 : q=795
  · subst q; decide +kernel
  by_cases e20 : q=796
  · subst q; decide +kernel
  by_cases e21 : q=797
  · subst q; decide +kernel
  by_cases e22 : q=798
  · subst q; decide +kernel
  by_cases e23 : q=799
  · subst q; decide +kernel
  by_cases e24 : q=800
  · subst q; decide +kernel
  by_cases e25 : q=801
  · subst q; decide +kernel
  by_cases e26 : q=802
  · subst q; decide +kernel
  by_cases e27 : q=803
  · subst q; decide +kernel
  by_cases e28 : q=804
  · subst q; decide +kernel
  by_cases e29 : q=805
  · subst q; decide +kernel
  by_cases e30 : q=1550
  · subst q; decide +kernel
  by_cases e31 : q=1551
  · subst q; decide +kernel
  by_cases e32 : q=1552
  · subst q; decide +kernel
  by_cases e33 : q=1553
  · subst q; decide +kernel
  by_cases e34 : q=1554
  · subst q; decide +kernel
  by_cases e35 : q=1556
  · subst q; decide +kernel
  by_cases e36 : q=1557
  · subst q; decide +kernel
  by_cases e37 : q=1558
  · subst q; decide +kernel
  by_cases e38 : q=1559
  · subst q; decide +kernel
  by_cases e39 : q=1560
  · subst q; decide +kernel
  simp only [port,low,if_false,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25,e26,e27,e28,e29,e30,e31,e32,e33,e34,e35,e36,e37,e38,e39]

def perm : Equiv.Perm Wire := ⟨port,port,twice,twice⟩

end ECDSAAdd.Entrant.TerminalFivePermutation
