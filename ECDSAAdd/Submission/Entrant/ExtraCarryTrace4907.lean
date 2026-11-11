import ECDSAAdd.Submission.Entrant.SixCarryTraceFacts
import ECDSAAdd.Submission.Entrant.SixCarryTraceChunks
import ECDSAAdd.Submission.Entrant.SixCarryBase
namespace ECDSAAdd.Entrant.ExtraCarryTrace4907
open ECDSAAdd SixCarryTrace SixCarryFrame SixCarryChunkViews SixCarryTraceChunks SixCarryTraceFacts
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] SixCarryFrame.prefixState SixCarryPrefixData.program

theorem nw_4116_4028_4073 : noWriteBetween SixCarryPrefixData.program 4028 4073 4116=true := by
 have h := noWrite_shift SixCarryPrefixData.program before31 (SixCarryPrefixData.chunk31++after31) 3968 60 105 4116 shape31 before_len31
 exact h.trans (by decide +kernel)

theorem nw_4339_0_4011 : noWriteBetween SixCarryPrefixData.program 0 4011 4339=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 4011 4339 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4340_0_4268 : noWriteBetween SixCarryPrefixData.program 0 4268 4340=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 4268 4340 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4341_0_4265 : noWriteBetween SixCarryPrefixData.program 0 4265 4341=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 4265 4341 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4344_0_2144 : noWriteBetween SixCarryPrefixData.program 0 2144 4344=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2144 4344 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4345_0_2150 : noWriteBetween SixCarryPrefixData.program 0 2150 4345=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2150 4345 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4346_0_2156 : noWriteBetween SixCarryPrefixData.program 0 2156 4346=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2156 4346 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4347_0_2162 : noWriteBetween SixCarryPrefixData.program 0 2162 4347=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2162 4347 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4348_0_2168 : noWriteBetween SixCarryPrefixData.program 0 2168 4348=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2168 4348 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4349_0_2174 : noWriteBetween SixCarryPrefixData.program 0 2174 4349=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2174 4349 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4350_0_2180 : noWriteBetween SixCarryPrefixData.program 0 2180 4350=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2180 4350 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4351_0_2186 : noWriteBetween SixCarryPrefixData.program 0 2186 4351=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2186 4351 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4352_0_2192 : noWriteBetween SixCarryPrefixData.program 0 2192 4352=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2192 4352 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4353_0_2198 : noWriteBetween SixCarryPrefixData.program 0 2198 4353=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2198 4353 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4354_0_2204 : noWriteBetween SixCarryPrefixData.program 0 2204 4354=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2204 4354 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4355_0_2210 : noWriteBetween SixCarryPrefixData.program 0 2210 4355=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2210 4355 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4356_0_2216 : noWriteBetween SixCarryPrefixData.program 0 2216 4356=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2216 4356 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4357_0_2222 : noWriteBetween SixCarryPrefixData.program 0 2222 4357=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2222 4357 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4358_0_2228 : noWriteBetween SixCarryPrefixData.program 0 2228 4358=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2228 4358 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4359_0_2234 : noWriteBetween SixCarryPrefixData.program 0 2234 4359=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2234 4359 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4360_0_2240 : noWriteBetween SixCarryPrefixData.program 0 2240 4360=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2240 4360 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4361_0_2246 : noWriteBetween SixCarryPrefixData.program 0 2246 4361=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 2246 4361 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4370_0_4890 : noWriteBetween SixCarryPrefixData.program 0 4890 4370=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 4890 4370 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4372_4020_4072 : noWriteBetween SixCarryPrefixData.program 4020 4072 4372=true := by
 have h := noWrite_shift SixCarryPrefixData.program before31 (SixCarryPrefixData.chunk31++after31) 3968 52 104 4372 shape31 before_len31
 exact h.trans (by decide +kernel)

theorem nw_4433_3827_4896 : noWriteBetween SixCarryPrefixData.program 3827 4896 4433=true := by
 have h := noWrite_shift SixCarryPrefixData.program before29 (SixCarryPrefixData.chunk29++after29) 3712 115 1184 4433 shape29 before_len29
 exact h.trans (by decide +kernel)

theorem nw_4434_3824_4902 : noWriteBetween SixCarryPrefixData.program 3824 4902 4434=true := by
 have h := noWrite_shift SixCarryPrefixData.program before29 (SixCarryPrefixData.chunk29++after29) 3712 112 1190 4434 shape29 before_len29
 exact h.trans (by decide +kernel)

theorem nw_4435_3821_4906 : noWriteBetween SixCarryPrefixData.program 3821 4906 4435=true := by
 have h := noWrite_shift SixCarryPrefixData.program before29 (SixCarryPrefixData.chunk29++after29) 3712 109 1194 4435 shape29 before_len29
 exact h.trans (by decide +kernel)

theorem nw_4469_0_737 : noWriteBetween SixCarryPrefixData.program 0 737 4469=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 737 4469 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4469_739_742 : noWriteBetween SixCarryPrefixData.program 739 742 4469=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 99 102 4469 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4469_743_745 : noWriteBetween SixCarryPrefixData.program 743 745 4469=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 103 105 4469 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4469_746_1021 : noWriteBetween SixCarryPrefixData.program 746 1021 4469=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 106 381 4469 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4470_0_743 : noWriteBetween SixCarryPrefixData.program 0 743 4470=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 743 4470 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4470_745_748 : noWriteBetween SixCarryPrefixData.program 745 748 4470=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 105 108 4470 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4470_749_751 : noWriteBetween SixCarryPrefixData.program 749 751 4470=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 109 111 4470 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4470_752_1018 : noWriteBetween SixCarryPrefixData.program 752 1018 4470=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 112 378 4470 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4473_767_769 : noWriteBetween SixCarryPrefixData.program 767 769 4473=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 127 129 4473 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4473_770_1009 : noWriteBetween SixCarryPrefixData.program 770 1009 4473=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 2 241 4473 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4474_0_767 : noWriteBetween SixCarryPrefixData.program 0 767 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 767 4474 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4474_769_772 : noWriteBetween SixCarryPrefixData.program 769 772 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 1 4 4474 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4474_773_775 : noWriteBetween SixCarryPrefixData.program 773 775 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 5 7 4474 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4474_776_1006 : noWriteBetween SixCarryPrefixData.program 776 1006 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 8 238 4474 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4474_1008_2143 : noWriteBetween SixCarryPrefixData.program 1008 2143 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 112 1247 4474 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4474_2145_2148 : noWriteBetween SixCarryPrefixData.program 2145 2148 4474=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 97 100 4474 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4475_0_773 : noWriteBetween SixCarryPrefixData.program 0 773 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 773 4475 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4475_775_778 : noWriteBetween SixCarryPrefixData.program 775 778 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 7 10 4475 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4475_779_781 : noWriteBetween SixCarryPrefixData.program 779 781 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 11 13 4475 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4475_782_1003 : noWriteBetween SixCarryPrefixData.program 782 1003 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 14 235 4475 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4475_1005_2149 : noWriteBetween SixCarryPrefixData.program 1005 2149 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 109 1253 4475 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4475_2151_2154 : noWriteBetween SixCarryPrefixData.program 2151 2154 4475=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 103 106 4475 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4476_0_779 : noWriteBetween SixCarryPrefixData.program 0 779 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 779 4476 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4476_781_784 : noWriteBetween SixCarryPrefixData.program 781 784 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 13 16 4476 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4476_785_787 : noWriteBetween SixCarryPrefixData.program 785 787 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 17 19 4476 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4476_788_1000 : noWriteBetween SixCarryPrefixData.program 788 1000 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 20 232 4476 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4476_1002_2155 : noWriteBetween SixCarryPrefixData.program 1002 2155 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 106 1259 4476 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4476_2157_2160 : noWriteBetween SixCarryPrefixData.program 2157 2160 4476=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 109 112 4476 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4477_0_785 : noWriteBetween SixCarryPrefixData.program 0 785 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 785 4477 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4477_787_790 : noWriteBetween SixCarryPrefixData.program 787 790 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 19 22 4477 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4477_791_793 : noWriteBetween SixCarryPrefixData.program 791 793 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 23 25 4477 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4477_794_997 : noWriteBetween SixCarryPrefixData.program 794 997 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 26 229 4477 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4477_999_2161 : noWriteBetween SixCarryPrefixData.program 999 2161 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 103 1265 4477 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4477_2163_2166 : noWriteBetween SixCarryPrefixData.program 2163 2166 4477=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 115 118 4477 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4478_0_791 : noWriteBetween SixCarryPrefixData.program 0 791 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 791 4478 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4478_793_796 : noWriteBetween SixCarryPrefixData.program 793 796 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 25 28 4478 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4478_797_799 : noWriteBetween SixCarryPrefixData.program 797 799 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 29 31 4478 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4478_800_994 : noWriteBetween SixCarryPrefixData.program 800 994 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 32 226 4478 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4478_996_2167 : noWriteBetween SixCarryPrefixData.program 996 2167 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 100 1271 4478 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4478_2169_2172 : noWriteBetween SixCarryPrefixData.program 2169 2172 4478=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 121 124 4478 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4479_0_797 : noWriteBetween SixCarryPrefixData.program 0 797 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 797 4479 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4479_799_802 : noWriteBetween SixCarryPrefixData.program 799 802 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 31 34 4479 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4479_803_805 : noWriteBetween SixCarryPrefixData.program 803 805 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 35 37 4479 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4479_806_991 : noWriteBetween SixCarryPrefixData.program 806 991 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 38 223 4479 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4479_993_2173 : noWriteBetween SixCarryPrefixData.program 993 2173 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 97 1277 4479 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4479_2175_2178 : noWriteBetween SixCarryPrefixData.program 2175 2178 4479=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 127 130 4479 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4480_0_803 : noWriteBetween SixCarryPrefixData.program 0 803 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 803 4480 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4480_805_808 : noWriteBetween SixCarryPrefixData.program 805 808 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 37 40 4480 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4480_809_811 : noWriteBetween SixCarryPrefixData.program 809 811 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 41 43 4480 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4480_812_988 : noWriteBetween SixCarryPrefixData.program 812 988 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 44 220 4480 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4480_990_2179 : noWriteBetween SixCarryPrefixData.program 990 2179 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 94 1283 4480 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4480_2181_2184 : noWriteBetween SixCarryPrefixData.program 2181 2184 4480=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 5 8 4480 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4481_0_809 : noWriteBetween SixCarryPrefixData.program 0 809 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 809 4481 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4481_811_814 : noWriteBetween SixCarryPrefixData.program 811 814 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 43 46 4481 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4481_815_817 : noWriteBetween SixCarryPrefixData.program 815 817 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 47 49 4481 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4481_818_985 : noWriteBetween SixCarryPrefixData.program 818 985 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 50 217 4481 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4481_987_2185 : noWriteBetween SixCarryPrefixData.program 987 2185 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 91 1289 4481 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4481_2187_2190 : noWriteBetween SixCarryPrefixData.program 2187 2190 4481=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 11 14 4481 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4482_0_815 : noWriteBetween SixCarryPrefixData.program 0 815 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 815 4482 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4482_817_820 : noWriteBetween SixCarryPrefixData.program 817 820 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 49 52 4482 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4482_821_823 : noWriteBetween SixCarryPrefixData.program 821 823 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 53 55 4482 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4482_824_982 : noWriteBetween SixCarryPrefixData.program 824 982 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 56 214 4482 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4482_984_2191 : noWriteBetween SixCarryPrefixData.program 984 2191 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 88 1295 4482 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4482_2193_2196 : noWriteBetween SixCarryPrefixData.program 2193 2196 4482=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 17 20 4482 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4483_0_821 : noWriteBetween SixCarryPrefixData.program 0 821 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 821 4483 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4483_823_826 : noWriteBetween SixCarryPrefixData.program 823 826 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 55 58 4483 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4483_827_829 : noWriteBetween SixCarryPrefixData.program 827 829 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 59 61 4483 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4483_830_979 : noWriteBetween SixCarryPrefixData.program 830 979 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 62 211 4483 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4483_981_2197 : noWriteBetween SixCarryPrefixData.program 981 2197 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 85 1301 4483 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4483_2199_2202 : noWriteBetween SixCarryPrefixData.program 2199 2202 4483=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 23 26 4483 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4484_0_827 : noWriteBetween SixCarryPrefixData.program 0 827 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 827 4484 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4484_829_832 : noWriteBetween SixCarryPrefixData.program 829 832 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 61 64 4484 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4484_833_835 : noWriteBetween SixCarryPrefixData.program 833 835 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 65 67 4484 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4484_836_976 : noWriteBetween SixCarryPrefixData.program 836 976 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 68 208 4484 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4484_978_2203 : noWriteBetween SixCarryPrefixData.program 978 2203 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 82 1307 4484 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4484_2205_2208 : noWriteBetween SixCarryPrefixData.program 2205 2208 4484=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 29 32 4484 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4485_0_833 : noWriteBetween SixCarryPrefixData.program 0 833 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 833 4485 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4485_835_838 : noWriteBetween SixCarryPrefixData.program 835 838 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 67 70 4485 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4485_839_841 : noWriteBetween SixCarryPrefixData.program 839 841 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 71 73 4485 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4485_842_973 : noWriteBetween SixCarryPrefixData.program 842 973 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 74 205 4485 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4485_975_2209 : noWriteBetween SixCarryPrefixData.program 975 2209 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 79 1313 4485 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4485_2211_2214 : noWriteBetween SixCarryPrefixData.program 2211 2214 4485=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 35 38 4485 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4486_0_839 : noWriteBetween SixCarryPrefixData.program 0 839 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 839 4486 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4486_841_844 : noWriteBetween SixCarryPrefixData.program 841 844 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 73 76 4486 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4486_845_847 : noWriteBetween SixCarryPrefixData.program 845 847 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 77 79 4486 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4486_848_970 : noWriteBetween SixCarryPrefixData.program 848 970 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 80 202 4486 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4486_972_2215 : noWriteBetween SixCarryPrefixData.program 972 2215 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 76 1319 4486 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4486_2217_2220 : noWriteBetween SixCarryPrefixData.program 2217 2220 4486=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 41 44 4486 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4487_0_845 : noWriteBetween SixCarryPrefixData.program 0 845 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 845 4487 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4487_847_850 : noWriteBetween SixCarryPrefixData.program 847 850 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 79 82 4487 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4487_851_853 : noWriteBetween SixCarryPrefixData.program 851 853 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 83 85 4487 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4487_854_967 : noWriteBetween SixCarryPrefixData.program 854 967 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 86 199 4487 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4487_969_2221 : noWriteBetween SixCarryPrefixData.program 969 2221 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 73 1325 4487 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4487_2223_2226 : noWriteBetween SixCarryPrefixData.program 2223 2226 4487=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 47 50 4487 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4488_0_851 : noWriteBetween SixCarryPrefixData.program 0 851 4488=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 851 4488 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4488_853_856 : noWriteBetween SixCarryPrefixData.program 853 856 4488=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 85 88 4488 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4488_966_2227 : noWriteBetween SixCarryPrefixData.program 966 2227 4488=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 70 1331 4488 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4488_2229_2232 : noWriteBetween SixCarryPrefixData.program 2229 2232 4488=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 53 56 4488 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4489_963_2233 : noWriteBetween SixCarryPrefixData.program 963 2233 4489=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 67 1337 4489 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4489_2235_2238 : noWriteBetween SixCarryPrefixData.program 2235 2238 4489=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 59 62 4489 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4490_960_2239 : noWriteBetween SixCarryPrefixData.program 960 2239 4490=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 64 1343 4490 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4490_2241_2244 : noWriteBetween SixCarryPrefixData.program 2241 2244 4490=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 65 68 4490 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4491_957_2245 : noWriteBetween SixCarryPrefixData.program 957 2245 4491=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 61 1349 4491 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4491_2247_2250 : noWriteBetween SixCarryPrefixData.program 2247 2250 4491=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 71 74 4491 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4492_954_2251 : noWriteBetween SixCarryPrefixData.program 954 2251 4492=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 58 1355 4492 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4492_2253_2256 : noWriteBetween SixCarryPrefixData.program 2253 2256 4492=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 77 80 4492 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4607_0_102 : noWriteBetween SixCarryPrefixData.program 0 102 4607=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 102 4607 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4607_103_735 : noWriteBetween SixCarryPrefixData.program 103 735 4607=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 103 735 4607 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4607_736_737 : noWriteBetween SixCarryPrefixData.program 736 737 4607=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 96 97 4607 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4608_0_103 : noWriteBetween SixCarryPrefixData.program 0 103 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 103 4608 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4608_104_741 : noWriteBetween SixCarryPrefixData.program 104 741 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 104 741 4608 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4608_742_746 : noWriteBetween SixCarryPrefixData.program 742 746 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 102 106 4608 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4608_747_1020 : noWriteBetween SixCarryPrefixData.program 747 1020 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 107 380 4608 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4608_1022_1414 : noWriteBetween SixCarryPrefixData.program 1022 1414 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 126 518 4608 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4608_1415_2141 : noWriteBetween SixCarryPrefixData.program 1415 2141 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 7 733 4608 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4608_2142_2143 : noWriteBetween SixCarryPrefixData.program 2142 2143 4608=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 94 95 4608 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4609_0_104 : noWriteBetween SixCarryPrefixData.program 0 104 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 104 4609 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4609_105_747 : noWriteBetween SixCarryPrefixData.program 105 747 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 105 747 4609 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4609_748_752 : noWriteBetween SixCarryPrefixData.program 748 752 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 108 112 4609 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4609_753_1017 : noWriteBetween SixCarryPrefixData.program 753 1017 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 113 377 4609 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4609_1019_1415 : noWriteBetween SixCarryPrefixData.program 1019 1415 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 123 519 4609 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4609_1416_2147 : noWriteBetween SixCarryPrefixData.program 1416 2147 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 8 739 4609 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4609_2148_2149 : noWriteBetween SixCarryPrefixData.program 2148 2149 4609=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 100 101 4609 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4610_2154_2155 : noWriteBetween SixCarryPrefixData.program 2154 2155 4610=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 106 107 4610 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4611_2160_2161 : noWriteBetween SixCarryPrefixData.program 2160 2161 4611=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 112 113 4611 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4612_766_770 : noWriteBetween SixCarryPrefixData.program 766 770 4612=true := by
 have h := noWrite_shift SixCarryPrefixData.program before5 (SixCarryPrefixData.chunk5++after5) 640 126 130 4612 shape5 before_len5
 exact h.trans (by decide +kernel)

theorem nw_4612_771_1008 : noWriteBetween SixCarryPrefixData.program 771 1008 4612=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 3 240 4612 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4612_1010_1418 : noWriteBetween SixCarryPrefixData.program 1010 1418 4612=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 114 522 4612 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4612_1419_2165 : noWriteBetween SixCarryPrefixData.program 1419 2165 4612=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 11 757 4612 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4612_2166_2167 : noWriteBetween SixCarryPrefixData.program 2166 2167 4612=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 118 119 4612 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4613_0_108 : noWriteBetween SixCarryPrefixData.program 0 108 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 108 4613 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4613_109_771 : noWriteBetween SixCarryPrefixData.program 109 771 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 109 771 4613 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4613_772_776 : noWriteBetween SixCarryPrefixData.program 772 776 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 4 8 4613 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4613_777_1005 : noWriteBetween SixCarryPrefixData.program 777 1005 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 9 237 4613 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4613_1007_1419 : noWriteBetween SixCarryPrefixData.program 1007 1419 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 111 523 4613 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4613_1420_2171 : noWriteBetween SixCarryPrefixData.program 1420 2171 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 12 763 4613 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4613_2172_2173 : noWriteBetween SixCarryPrefixData.program 2172 2173 4613=true := by
 have h := noWrite_shift SixCarryPrefixData.program before16 (SixCarryPrefixData.chunk16++after16) 2048 124 125 4613 shape16 before_len16
 exact h.trans (by decide +kernel)

theorem nw_4614_0_109 : noWriteBetween SixCarryPrefixData.program 0 109 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 109 4614 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4614_110_777 : noWriteBetween SixCarryPrefixData.program 110 777 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 110 777 4614 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4614_778_782 : noWriteBetween SixCarryPrefixData.program 778 782 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 10 14 4614 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4614_783_1002 : noWriteBetween SixCarryPrefixData.program 783 1002 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 15 234 4614 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4614_1004_1420 : noWriteBetween SixCarryPrefixData.program 1004 1420 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 108 524 4614 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4614_1421_2177 : noWriteBetween SixCarryPrefixData.program 1421 2177 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 13 769 4614 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4614_2178_2179 : noWriteBetween SixCarryPrefixData.program 2178 2179 4614=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 2 3 4614 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4615_0_110 : noWriteBetween SixCarryPrefixData.program 0 110 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 110 4615 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4615_111_783 : noWriteBetween SixCarryPrefixData.program 111 783 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 111 783 4615 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4615_784_788 : noWriteBetween SixCarryPrefixData.program 784 788 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 16 20 4615 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4615_789_999 : noWriteBetween SixCarryPrefixData.program 789 999 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 21 231 4615 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4615_1001_1421 : noWriteBetween SixCarryPrefixData.program 1001 1421 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 105 525 4615 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4615_1422_2183 : noWriteBetween SixCarryPrefixData.program 1422 2183 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 14 775 4615 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4615_2184_2185 : noWriteBetween SixCarryPrefixData.program 2184 2185 4615=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 8 9 4615 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4616_0_111 : noWriteBetween SixCarryPrefixData.program 0 111 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 111 4616 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4616_112_789 : noWriteBetween SixCarryPrefixData.program 112 789 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 112 789 4616 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4616_790_794 : noWriteBetween SixCarryPrefixData.program 790 794 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 22 26 4616 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4616_795_996 : noWriteBetween SixCarryPrefixData.program 795 996 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 27 228 4616 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4616_998_1422 : noWriteBetween SixCarryPrefixData.program 998 1422 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 102 526 4616 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4616_1423_2189 : noWriteBetween SixCarryPrefixData.program 1423 2189 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 15 781 4616 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4616_2190_2191 : noWriteBetween SixCarryPrefixData.program 2190 2191 4616=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 14 15 4616 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4617_0_112 : noWriteBetween SixCarryPrefixData.program 0 112 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 112 4617 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4617_113_795 : noWriteBetween SixCarryPrefixData.program 113 795 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 113 795 4617 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4617_796_800 : noWriteBetween SixCarryPrefixData.program 796 800 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 28 32 4617 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4617_801_993 : noWriteBetween SixCarryPrefixData.program 801 993 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 33 225 4617 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4617_995_1423 : noWriteBetween SixCarryPrefixData.program 995 1423 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 99 527 4617 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4617_1424_2195 : noWriteBetween SixCarryPrefixData.program 1424 2195 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 16 787 4617 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4617_2196_2197 : noWriteBetween SixCarryPrefixData.program 2196 2197 4617=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 20 21 4617 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4618_0_113 : noWriteBetween SixCarryPrefixData.program 0 113 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 113 4618 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4618_114_801 : noWriteBetween SixCarryPrefixData.program 114 801 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 114 801 4618 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4618_802_806 : noWriteBetween SixCarryPrefixData.program 802 806 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 34 38 4618 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4618_807_990 : noWriteBetween SixCarryPrefixData.program 807 990 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 39 222 4618 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4618_992_1424 : noWriteBetween SixCarryPrefixData.program 992 1424 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 96 528 4618 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4618_1425_2201 : noWriteBetween SixCarryPrefixData.program 1425 2201 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 17 793 4618 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4618_2202_2203 : noWriteBetween SixCarryPrefixData.program 2202 2203 4618=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 26 27 4618 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4619_0_114 : noWriteBetween SixCarryPrefixData.program 0 114 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 114 4619 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4619_115_807 : noWriteBetween SixCarryPrefixData.program 115 807 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 115 807 4619 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4619_808_812 : noWriteBetween SixCarryPrefixData.program 808 812 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 40 44 4619 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4619_813_987 : noWriteBetween SixCarryPrefixData.program 813 987 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 45 219 4619 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4619_989_1425 : noWriteBetween SixCarryPrefixData.program 989 1425 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 93 529 4619 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4619_1426_2207 : noWriteBetween SixCarryPrefixData.program 1426 2207 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 18 799 4619 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4619_2208_2209 : noWriteBetween SixCarryPrefixData.program 2208 2209 4619=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 32 33 4619 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4620_0_115 : noWriteBetween SixCarryPrefixData.program 0 115 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 115 4620 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4620_116_813 : noWriteBetween SixCarryPrefixData.program 116 813 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 116 813 4620 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4620_814_818 : noWriteBetween SixCarryPrefixData.program 814 818 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 46 50 4620 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4620_819_984 : noWriteBetween SixCarryPrefixData.program 819 984 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 51 216 4620 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4620_986_1426 : noWriteBetween SixCarryPrefixData.program 986 1426 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 90 530 4620 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4620_1427_2213 : noWriteBetween SixCarryPrefixData.program 1427 2213 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 19 805 4620 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4620_2214_2215 : noWriteBetween SixCarryPrefixData.program 2214 2215 4620=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 38 39 4620 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4621_0_116 : noWriteBetween SixCarryPrefixData.program 0 116 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 116 4621 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4621_117_819 : noWriteBetween SixCarryPrefixData.program 117 819 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 117 819 4621 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4621_820_824 : noWriteBetween SixCarryPrefixData.program 820 824 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 52 56 4621 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4621_825_981 : noWriteBetween SixCarryPrefixData.program 825 981 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 57 213 4621 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4621_983_1427 : noWriteBetween SixCarryPrefixData.program 983 1427 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 87 531 4621 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4621_1428_2219 : noWriteBetween SixCarryPrefixData.program 1428 2219 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 20 811 4621 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4621_2220_2221 : noWriteBetween SixCarryPrefixData.program 2220 2221 4621=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 44 45 4621 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4622_0_117 : noWriteBetween SixCarryPrefixData.program 0 117 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 117 4622 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4622_118_825 : noWriteBetween SixCarryPrefixData.program 118 825 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 118 825 4622 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4622_826_830 : noWriteBetween SixCarryPrefixData.program 826 830 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 58 62 4622 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4622_831_978 : noWriteBetween SixCarryPrefixData.program 831 978 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 63 210 4622 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4622_980_1428 : noWriteBetween SixCarryPrefixData.program 980 1428 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 84 532 4622 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4622_1429_2225 : noWriteBetween SixCarryPrefixData.program 1429 2225 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 21 817 4622 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4622_2226_2227 : noWriteBetween SixCarryPrefixData.program 2226 2227 4622=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 50 51 4622 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4623_0_118 : noWriteBetween SixCarryPrefixData.program 0 118 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 118 4623 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4623_119_831 : noWriteBetween SixCarryPrefixData.program 119 831 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 119 831 4623 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4623_832_836 : noWriteBetween SixCarryPrefixData.program 832 836 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 64 68 4623 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4623_837_975 : noWriteBetween SixCarryPrefixData.program 837 975 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 69 207 4623 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4623_977_1429 : noWriteBetween SixCarryPrefixData.program 977 1429 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 81 533 4623 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4623_1430_2231 : noWriteBetween SixCarryPrefixData.program 1430 2231 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 22 823 4623 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4623_2232_2233 : noWriteBetween SixCarryPrefixData.program 2232 2233 4623=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 56 57 4623 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4624_0_119 : noWriteBetween SixCarryPrefixData.program 0 119 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 119 4624 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4624_120_837 : noWriteBetween SixCarryPrefixData.program 120 837 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 120 837 4624 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4624_838_842 : noWriteBetween SixCarryPrefixData.program 838 842 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 70 74 4624 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4624_843_972 : noWriteBetween SixCarryPrefixData.program 843 972 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 75 204 4624 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4624_974_1430 : noWriteBetween SixCarryPrefixData.program 974 1430 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 78 534 4624 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4624_1431_2237 : noWriteBetween SixCarryPrefixData.program 1431 2237 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 23 829 4624 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4624_2238_2239 : noWriteBetween SixCarryPrefixData.program 2238 2239 4624=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 62 63 4624 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4625_0_120 : noWriteBetween SixCarryPrefixData.program 0 120 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 120 4625 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4625_121_843 : noWriteBetween SixCarryPrefixData.program 121 843 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 121 843 4625 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4625_844_848 : noWriteBetween SixCarryPrefixData.program 844 848 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 76 80 4625 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4625_849_969 : noWriteBetween SixCarryPrefixData.program 849 969 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 81 201 4625 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4625_971_1431 : noWriteBetween SixCarryPrefixData.program 971 1431 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 75 535 4625 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4625_1432_2243 : noWriteBetween SixCarryPrefixData.program 1432 2243 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 24 835 4625 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4625_2244_2245 : noWriteBetween SixCarryPrefixData.program 2244 2245 4625=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 68 69 4625 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4626_0_121 : noWriteBetween SixCarryPrefixData.program 0 121 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 0 121 4626 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4626_122_849 : noWriteBetween SixCarryPrefixData.program 122 849 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before0 (SixCarryPrefixData.chunk0++after0) 0 122 849 4626 shape0 before_len0
 exact h.trans (by decide +kernel)

theorem nw_4626_850_854 : noWriteBetween SixCarryPrefixData.program 850 854 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 82 86 4626 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4626_855_966 : noWriteBetween SixCarryPrefixData.program 855 966 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before6 (SixCarryPrefixData.chunk6++after6) 768 87 198 4626 shape6 before_len6
 exact h.trans (by decide +kernel)

theorem nw_4626_968_1432 : noWriteBetween SixCarryPrefixData.program 968 1432 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before7 (SixCarryPrefixData.chunk7++after7) 896 72 536 4626 shape7 before_len7
 exact h.trans (by decide +kernel)

theorem nw_4626_1433_2249 : noWriteBetween SixCarryPrefixData.program 1433 2249 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before11 (SixCarryPrefixData.chunk11++after11) 1408 25 841 4626 shape11 before_len11
 exact h.trans (by decide +kernel)

theorem nw_4626_2250_2251 : noWriteBetween SixCarryPrefixData.program 2250 2251 4626=true := by
 have h := noWrite_shift SixCarryPrefixData.program before17 (SixCarryPrefixData.chunk17++after17) 2176 74 75 4626 shape17 before_len17
 exact h.trans (by decide +kernel)

theorem nw_4630_4275_4307 : noWriteBetween SixCarryPrefixData.program 4275 4307 4630=true := by
 have h := noWrite_shift SixCarryPrefixData.program before33 (SixCarryPrefixData.chunk33++after33) 4224 51 83 4630 shape33 before_len33
 exact h.trans (by decide +kernel)

theorem nw_4631_4276_4308 : noWriteBetween SixCarryPrefixData.program 4276 4308 4631=true := by
 have h := noWrite_shift SixCarryPrefixData.program before33 (SixCarryPrefixData.chunk33++after33) 4224 52 84 4631 shape33 before_len33
 exact h.trans (by decide +kernel)

theorem nw_4660_4888_4889 : noWriteBetween SixCarryPrefixData.program 4888 4889 4660=true := by
 have h := noWrite_shift SixCarryPrefixData.program before38 (SixCarryPrefixData.chunk38++after38) 4864 24 25 4660 shape38 before_len38
 exact h.trans (by decide +kernel)

theorem nw_4661_4894_4895 : noWriteBetween SixCarryPrefixData.program 4894 4895 4661=true := by
 have h := noWrite_shift SixCarryPrefixData.program before38 (SixCarryPrefixData.chunk38++after38) 4864 30 31 4661 shape38 before_len38
 exact h.trans (by decide +kernel)

theorem nw_4662_4900_4901 : noWriteBetween SixCarryPrefixData.program 4900 4901 4662=true := by
 have h := noWrite_shift SixCarryPrefixData.program before38 (SixCarryPrefixData.chunk38++after38) 4864 36 37 4662 shape38 before_len38
 exact h.trans (by decide +kernel)

theorem nw_4663_4906_4907 : noWriteBetween SixCarryPrefixData.program 4906 4907 4663=true := by
 have h := noWrite_shift SixCarryPrefixData.program before38 (SixCarryPrefixData.chunk38++after38) 4864 42 43 4663 shape38 before_len38
 exact h.trans (by decide +kernel)

theorem frame_4339_0_735 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 735 basis 4339=prefixState SixCarryPrefixData.program 0 basis 4339 := by
 exact at_between SixCarryPrefixData.program 0 735 4339 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4011 735 4339 (by decide +kernel) nw_4339_0_4011) basis

theorem frame_4339_0_738 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 738 basis 4339=prefixState SixCarryPrefixData.program 0 basis 4339 := by
 exact at_between SixCarryPrefixData.program 0 738 4339 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4011 738 4339 (by decide +kernel) nw_4339_0_4011) basis

theorem frame_4340_0_741 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 741 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 741 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 741 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4340_0_742 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 742 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 742 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 742 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4340_0_744 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 744 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 744 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 744 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4340_0_745 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 745 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 745 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 745 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4340_0_746 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 746 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 746 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 746 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4340_0_1020 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1020 basis 4340=prefixState SixCarryPrefixData.program 0 basis 4340 := by
 exact at_between SixCarryPrefixData.program 0 1020 4340 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4268 1020 4340 (by decide +kernel) nw_4340_0_4268) basis

theorem frame_4341_0_747 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 747 basis 4341=prefixState SixCarryPrefixData.program 0 basis 4341 := by
 exact at_between SixCarryPrefixData.program 0 747 4341 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4265 747 4341 (by decide +kernel) nw_4341_0_4265) basis

theorem frame_4341_0_748 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 748 basis 4341=prefixState SixCarryPrefixData.program 0 basis 4341 := by
 exact at_between SixCarryPrefixData.program 0 748 4341 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4265 748 4341 (by decide +kernel) nw_4341_0_4265) basis

theorem frame_4341_0_751 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 751 basis 4341=prefixState SixCarryPrefixData.program 0 basis 4341 := by
 exact at_between SixCarryPrefixData.program 0 751 4341 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4265 751 4341 (by decide +kernel) nw_4341_0_4265) basis

theorem frame_4341_0_752 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 752 basis 4341=prefixState SixCarryPrefixData.program 0 basis 4341 := by
 exact at_between SixCarryPrefixData.program 0 752 4341 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4265 752 4341 (by decide +kernel) nw_4341_0_4265) basis

theorem frame_4341_0_1017 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1017 basis 4341=prefixState SixCarryPrefixData.program 0 basis 4341 := by
 exact at_between SixCarryPrefixData.program 0 1017 4341 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4265 1017 4341 (by decide +kernel) nw_4341_0_4265) basis

theorem frame_4344_0_768 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 768 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 768 4344 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2144 768 4344 (by decide +kernel) nw_4344_0_2144) basis

theorem frame_4344_0_769 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 769 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 769 4344 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2144 769 4344 (by decide +kernel) nw_4344_0_2144) basis

theorem frame_4344_0_770 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 770 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 770 4344 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2144 770 4344 (by decide +kernel) nw_4344_0_2144) basis

theorem frame_4344_0_1008 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1008 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 1008 4344 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2144 1008 4344 (by decide +kernel) nw_4344_0_2144) basis

theorem frame_4344_0_2141 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2141 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 2141 4344 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2144 2141 4344 (by decide +kernel) nw_4344_0_2144) basis

theorem frame_4344_0_2144 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2144 basis 4344=prefixState SixCarryPrefixData.program 0 basis 4344 := by
 exact at_between SixCarryPrefixData.program 0 2144 4344 (by decide +kernel) nw_4344_0_2144 basis

theorem frame_4345_0_102 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 102 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 102 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 102 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_771 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 771 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 771 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 771 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_772 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 772 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 772 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 772 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_774 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 774 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 774 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 774 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_775 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 775 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 775 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 775 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_776 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 776 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 776 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 776 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_1005 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1005 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 1005 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 1005 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_2147 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2147 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 2147 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 2147 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_2148 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2148 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 2148 4345 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2150 2148 4345 (by decide +kernel) nw_4345_0_2150) basis

theorem frame_4345_0_2150 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2150 basis 4345=prefixState SixCarryPrefixData.program 0 basis 4345 := by
 exact at_between SixCarryPrefixData.program 0 2150 4345 (by decide +kernel) nw_4345_0_2150 basis

theorem frame_4346_0_103 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 103 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 103 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 103 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_777 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 777 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 777 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 777 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_778 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 778 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 778 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 778 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_780 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 780 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 780 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 780 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_781 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 781 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 781 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 781 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_782 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 782 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 782 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 782 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_1002 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1002 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 1002 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 1002 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_2154 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2154 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 2154 4346 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2156 2154 4346 (by decide +kernel) nw_4346_0_2156) basis

theorem frame_4346_0_2156 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2156 basis 4346=prefixState SixCarryPrefixData.program 0 basis 4346 := by
 exact at_between SixCarryPrefixData.program 0 2156 4346 (by decide +kernel) nw_4346_0_2156 basis

theorem frame_4347_0_104 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 104 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 104 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 104 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_783 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 783 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 783 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 783 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_784 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 784 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 784 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 784 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_786 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 786 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 786 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 786 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_787 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 787 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 787 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 787 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_788 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 788 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 788 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 788 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_999 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 999 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 999 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 999 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_2160 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2160 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 2160 4347 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2162 2160 4347 (by decide +kernel) nw_4347_0_2162) basis

theorem frame_4347_0_2162 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2162 basis 4347=prefixState SixCarryPrefixData.program 0 basis 4347 := by
 exact at_between SixCarryPrefixData.program 0 2162 4347 (by decide +kernel) nw_4347_0_2162 basis

theorem frame_4348_0_789 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 789 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 789 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 789 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_790 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 790 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 790 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 790 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_792 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 792 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 792 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 792 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_793 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 793 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 793 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 793 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_794 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 794 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 794 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 794 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_996 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 996 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 996 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 996 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_2165 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2165 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 2165 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 2165 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_2166 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2166 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 2166 4348 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2168 2166 4348 (by decide +kernel) nw_4348_0_2168) basis

theorem frame_4348_0_2168 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2168 basis 4348=prefixState SixCarryPrefixData.program 0 basis 4348 := by
 exact at_between SixCarryPrefixData.program 0 2168 4348 (by decide +kernel) nw_4348_0_2168 basis

theorem frame_4349_0_795 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 795 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 795 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 795 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_796 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 796 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 796 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 796 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_798 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 798 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 798 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 798 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_799 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 799 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 799 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 799 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_800 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 800 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 800 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 800 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_993 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 993 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 993 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 993 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_2171 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2171 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 2171 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 2171 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_2172 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2172 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 2172 4349 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2174 2172 4349 (by decide +kernel) nw_4349_0_2174) basis

theorem frame_4349_0_2174 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2174 basis 4349=prefixState SixCarryPrefixData.program 0 basis 4349 := by
 exact at_between SixCarryPrefixData.program 0 2174 4349 (by decide +kernel) nw_4349_0_2174 basis

theorem frame_4350_0_801 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 801 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 801 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 801 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_802 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 802 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 802 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 802 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_804 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 804 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 804 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 804 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_805 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 805 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 805 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 805 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_806 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 806 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 806 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 806 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_990 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 990 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 990 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 990 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_2177 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2177 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 2177 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 2177 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_2178 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2178 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 2178 4350 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2180 2178 4350 (by decide +kernel) nw_4350_0_2180) basis

theorem frame_4350_0_2180 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2180 basis 4350=prefixState SixCarryPrefixData.program 0 basis 4350 := by
 exact at_between SixCarryPrefixData.program 0 2180 4350 (by decide +kernel) nw_4350_0_2180 basis

theorem frame_4351_0_108 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 108 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 108 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 108 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_807 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 807 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 807 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 807 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_808 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 808 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 808 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 808 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_810 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 810 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 810 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 810 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_811 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 811 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 811 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 811 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_812 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 812 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 812 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 812 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_987 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 987 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 987 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 987 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_2183 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2183 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 2183 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 2183 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_2184 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2184 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 2184 4351 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2186 2184 4351 (by decide +kernel) nw_4351_0_2186) basis

theorem frame_4351_0_2186 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2186 basis 4351=prefixState SixCarryPrefixData.program 0 basis 4351 := by
 exact at_between SixCarryPrefixData.program 0 2186 4351 (by decide +kernel) nw_4351_0_2186 basis

theorem frame_4352_0_109 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 109 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 109 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 109 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_813 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 813 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 813 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 813 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_814 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 814 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 814 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 814 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_816 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 816 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 816 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 816 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_817 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 817 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 817 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 817 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_818 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 818 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 818 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 818 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_984 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 984 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 984 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 984 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_2189 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2189 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 2189 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 2189 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_2190 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2190 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 2190 4352 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2192 2190 4352 (by decide +kernel) nw_4352_0_2192) basis

theorem frame_4352_0_2192 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2192 basis 4352=prefixState SixCarryPrefixData.program 0 basis 4352 := by
 exact at_between SixCarryPrefixData.program 0 2192 4352 (by decide +kernel) nw_4352_0_2192 basis

theorem frame_4353_0_110 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 110 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 110 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 110 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_819 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 819 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 819 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 819 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_820 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 820 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 820 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 820 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_822 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 822 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 822 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 822 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_823 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 823 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 823 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 823 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_824 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 824 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 824 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 824 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_981 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 981 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 981 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 981 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_2195 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2195 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 2195 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 2195 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_2196 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2196 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 2196 4353 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2198 2196 4353 (by decide +kernel) nw_4353_0_2198) basis

theorem frame_4353_0_2198 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2198 basis 4353=prefixState SixCarryPrefixData.program 0 basis 4353 := by
 exact at_between SixCarryPrefixData.program 0 2198 4353 (by decide +kernel) nw_4353_0_2198 basis

theorem frame_4354_0_111 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 111 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 111 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 111 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_825 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 825 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 825 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 825 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_826 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 826 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 826 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 826 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_828 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 828 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 828 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 828 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_829 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 829 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 829 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 829 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_830 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 830 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 830 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 830 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_978 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 978 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 978 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 978 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_2201 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2201 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 2201 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 2201 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_2202 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2202 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 2202 4354 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2204 2202 4354 (by decide +kernel) nw_4354_0_2204) basis

theorem frame_4354_0_2204 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2204 basis 4354=prefixState SixCarryPrefixData.program 0 basis 4354 := by
 exact at_between SixCarryPrefixData.program 0 2204 4354 (by decide +kernel) nw_4354_0_2204 basis

theorem frame_4355_0_112 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 112 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 112 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 112 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_831 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 831 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 831 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 831 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_832 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 832 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 832 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 832 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_834 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 834 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 834 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 834 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_835 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 835 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 835 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 835 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_836 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 836 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 836 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 836 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_975 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 975 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 975 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 975 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_2207 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2207 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 2207 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 2207 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_2208 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2208 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 2208 4355 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2210 2208 4355 (by decide +kernel) nw_4355_0_2210) basis

theorem frame_4355_0_2210 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2210 basis 4355=prefixState SixCarryPrefixData.program 0 basis 4355 := by
 exact at_between SixCarryPrefixData.program 0 2210 4355 (by decide +kernel) nw_4355_0_2210 basis

theorem frame_4356_0_113 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 113 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 113 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 113 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_837 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 837 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 837 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 837 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_838 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 838 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 838 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 838 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_840 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 840 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 840 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 840 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_841 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 841 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 841 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 841 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_842 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 842 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 842 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 842 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_972 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 972 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 972 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 972 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_2213 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2213 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 2213 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 2213 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_2214 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2214 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 2214 4356 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2216 2214 4356 (by decide +kernel) nw_4356_0_2216) basis

theorem frame_4356_0_2216 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2216 basis 4356=prefixState SixCarryPrefixData.program 0 basis 4356 := by
 exact at_between SixCarryPrefixData.program 0 2216 4356 (by decide +kernel) nw_4356_0_2216 basis

theorem frame_4357_0_114 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 114 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 114 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 114 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_843 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 843 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 843 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 843 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_844 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 844 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 844 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 844 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_846 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 846 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 846 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 846 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_847 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 847 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 847 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 847 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_848 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 848 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 848 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 848 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_969 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 969 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 969 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 969 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_2219 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2219 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 2219 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 2219 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_2220 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2220 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 2220 4357 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2222 2220 4357 (by decide +kernel) nw_4357_0_2222) basis

theorem frame_4357_0_2222 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2222 basis 4357=prefixState SixCarryPrefixData.program 0 basis 4357 := by
 exact at_between SixCarryPrefixData.program 0 2222 4357 (by decide +kernel) nw_4357_0_2222 basis

theorem frame_4358_0_115 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 115 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 115 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 115 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_849 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 849 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 849 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 849 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_850 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 850 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 850 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 850 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_852 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 852 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 852 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 852 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_853 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 853 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 853 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 853 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_854 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 854 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 854 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 854 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_966 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 966 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 966 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 966 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_2225 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2225 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 2225 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 2225 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_2226 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2226 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 2226 4358 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2228 2226 4358 (by decide +kernel) nw_4358_0_2228) basis

theorem frame_4358_0_2228 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2228 basis 4358=prefixState SixCarryPrefixData.program 0 basis 4358 := by
 exact at_between SixCarryPrefixData.program 0 2228 4358 (by decide +kernel) nw_4358_0_2228 basis

theorem frame_4359_0_116 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 116 basis 4359=prefixState SixCarryPrefixData.program 0 basis 4359 := by
 exact at_between SixCarryPrefixData.program 0 116 4359 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2234 116 4359 (by decide +kernel) nw_4359_0_2234) basis

theorem frame_4359_0_856 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 856 basis 4359=prefixState SixCarryPrefixData.program 0 basis 4359 := by
 exact at_between SixCarryPrefixData.program 0 856 4359 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2234 856 4359 (by decide +kernel) nw_4359_0_2234) basis

theorem frame_4359_0_2231 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2231 basis 4359=prefixState SixCarryPrefixData.program 0 basis 4359 := by
 exact at_between SixCarryPrefixData.program 0 2231 4359 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2234 2231 4359 (by decide +kernel) nw_4359_0_2234) basis

theorem frame_4359_0_2232 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2232 basis 4359=prefixState SixCarryPrefixData.program 0 basis 4359 := by
 exact at_between SixCarryPrefixData.program 0 2232 4359 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2234 2232 4359 (by decide +kernel) nw_4359_0_2234) basis

theorem frame_4359_0_2234 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2234 basis 4359=prefixState SixCarryPrefixData.program 0 basis 4359 := by
 exact at_between SixCarryPrefixData.program 0 2234 4359 (by decide +kernel) nw_4359_0_2234 basis

theorem frame_4360_0_117 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 117 basis 4360=prefixState SixCarryPrefixData.program 0 basis 4360 := by
 exact at_between SixCarryPrefixData.program 0 117 4360 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2240 117 4360 (by decide +kernel) nw_4360_0_2240) basis

theorem frame_4360_0_2237 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2237 basis 4360=prefixState SixCarryPrefixData.program 0 basis 4360 := by
 exact at_between SixCarryPrefixData.program 0 2237 4360 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2240 2237 4360 (by decide +kernel) nw_4360_0_2240) basis

theorem frame_4360_0_2238 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2238 basis 4360=prefixState SixCarryPrefixData.program 0 basis 4360 := by
 exact at_between SixCarryPrefixData.program 0 2238 4360 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2240 2238 4360 (by decide +kernel) nw_4360_0_2240) basis

theorem frame_4360_0_2240 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2240 basis 4360=prefixState SixCarryPrefixData.program 0 basis 4360 := by
 exact at_between SixCarryPrefixData.program 0 2240 4360 (by decide +kernel) nw_4360_0_2240 basis

theorem frame_4361_0_118 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 118 basis 4361=prefixState SixCarryPrefixData.program 0 basis 4361 := by
 exact at_between SixCarryPrefixData.program 0 118 4361 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2246 118 4361 (by decide +kernel) nw_4361_0_2246) basis

theorem frame_4361_0_2243 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2243 basis 4361=prefixState SixCarryPrefixData.program 0 basis 4361 := by
 exact at_between SixCarryPrefixData.program 0 2243 4361 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2246 2243 4361 (by decide +kernel) nw_4361_0_2246) basis

theorem frame_4361_0_2244 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2244 basis 4361=prefixState SixCarryPrefixData.program 0 basis 4361 := by
 exact at_between SixCarryPrefixData.program 0 2244 4361 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 2246 2244 4361 (by decide +kernel) nw_4361_0_2246) basis

theorem frame_4361_0_2246 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2246 basis 4361=prefixState SixCarryPrefixData.program 0 basis 4361 := by
 exact at_between SixCarryPrefixData.program 0 2246 4361 (by decide +kernel) nw_4361_0_2246 basis

theorem frame_4362_0_119 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 119 basis 4362=prefixState SixCarryPrefixData.program 0 basis 4362 := by
 exact at_between SixCarryPrefixData.program 0 119 4362 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4842 119 4362 (by decide +kernel) nw_4362_0_4842) basis

theorem frame_4362_0_2249 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2249 basis 4362=prefixState SixCarryPrefixData.program 0 basis 4362 := by
 exact at_between SixCarryPrefixData.program 0 2249 4362 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4842 2249 4362 (by decide +kernel) nw_4362_0_4842) basis

theorem frame_4362_0_2250 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2250 basis 4362=prefixState SixCarryPrefixData.program 0 basis 4362 := by
 exact at_between SixCarryPrefixData.program 0 2250 4362 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4842 2250 4362 (by decide +kernel) nw_4362_0_4842) basis

theorem frame_4362_0_2252 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2252 basis 4362=prefixState SixCarryPrefixData.program 0 basis 4362 := by
 exact at_between SixCarryPrefixData.program 0 2252 4362 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4842 2252 4362 (by decide +kernel) nw_4362_0_4842) basis

theorem frame_4363_0_120 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 120 basis 4363=prefixState SixCarryPrefixData.program 0 basis 4363 := by
 exact at_between SixCarryPrefixData.program 0 120 4363 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4848 120 4363 (by decide +kernel) nw_4363_0_4848) basis

theorem frame_4363_0_2256 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2256 basis 4363=prefixState SixCarryPrefixData.program 0 basis 4363 := by
 exact at_between SixCarryPrefixData.program 0 2256 4363 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4848 2256 4363 (by decide +kernel) nw_4363_0_4848) basis

theorem frame_4364_0_121 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 121 basis 4364=prefixState SixCarryPrefixData.program 0 basis 4364 := by
 exact at_between SixCarryPrefixData.program 0 121 4364 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 0 4854 121 4364 (by decide +kernel) nw_4364_0_4854) basis

theorem frame_4468_737_737 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 737 basis 4468=prefixState SixCarryPrefixData.program 737 basis 4468 := by
 rfl

theorem frame_4469_0_737 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 737 basis 4469=prefixState SixCarryPrefixData.program 0 basis 4469 := by
 exact at_between SixCarryPrefixData.program 0 737 4469 (by decide +kernel) nw_4469_0_737 basis

theorem frame_4469_738_738 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 738 basis 4469=prefixState SixCarryPrefixData.program 738 basis 4469 := by
 rfl

theorem frame_4469_739_742 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 742 basis 4469=prefixState SixCarryPrefixData.program 739 basis 4469 := by
 exact at_between SixCarryPrefixData.program 739 742 4469 (by decide +kernel) nw_4469_739_742 basis

theorem frame_4469_743_743 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 743 basis 4469=prefixState SixCarryPrefixData.program 743 basis 4469 := by
 rfl

theorem frame_4469_743_745 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 745 basis 4469=prefixState SixCarryPrefixData.program 743 basis 4469 := by
 exact at_between SixCarryPrefixData.program 743 745 4469 (by decide +kernel) nw_4469_743_745 basis

theorem frame_4469_746_1021 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1021 basis 4469=prefixState SixCarryPrefixData.program 746 basis 4469 := by
 exact at_between SixCarryPrefixData.program 746 1021 4469 (by decide +kernel) nw_4469_746_1021 basis

theorem frame_4470_0_743 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 743 basis 4470=prefixState SixCarryPrefixData.program 0 basis 4470 := by
 exact at_between SixCarryPrefixData.program 0 743 4470 (by decide +kernel) nw_4470_0_743 basis

theorem frame_4470_744_744 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 744 basis 4470=prefixState SixCarryPrefixData.program 744 basis 4470 := by
 rfl

theorem frame_4470_745_748 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 748 basis 4470=prefixState SixCarryPrefixData.program 745 basis 4470 := by
 exact at_between SixCarryPrefixData.program 745 748 4470 (by decide +kernel) nw_4470_745_748 basis

theorem frame_4470_749_751 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 751 basis 4470=prefixState SixCarryPrefixData.program 749 basis 4470 := by
 exact at_between SixCarryPrefixData.program 749 751 4470 (by decide +kernel) nw_4470_749_751 basis

theorem frame_4470_752_1018 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1018 basis 4470=prefixState SixCarryPrefixData.program 752 basis 4470 := by
 exact at_between SixCarryPrefixData.program 752 1018 4470 (by decide +kernel) nw_4470_752_1018 basis

theorem frame_4473_767_767 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 767 basis 4473=prefixState SixCarryPrefixData.program 767 basis 4473 := by
 rfl

theorem frame_4473_767_769 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 769 basis 4473=prefixState SixCarryPrefixData.program 767 basis 4473 := by
 exact at_between SixCarryPrefixData.program 767 769 4473 (by decide +kernel) nw_4473_767_769 basis

theorem frame_4473_770_1009 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1009 basis 4473=prefixState SixCarryPrefixData.program 770 basis 4473 := by
 exact at_between SixCarryPrefixData.program 770 1009 4473 (by decide +kernel) nw_4473_770_1009 basis

theorem frame_4473_2143_2143 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2143 basis 4473=prefixState SixCarryPrefixData.program 2143 basis 4473 := by
 rfl

theorem frame_4474_0_767 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 767 basis 4474=prefixState SixCarryPrefixData.program 0 basis 4474 := by
 exact at_between SixCarryPrefixData.program 0 767 4474 (by decide +kernel) nw_4474_0_767 basis

theorem frame_4474_768_768 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 768 basis 4474=prefixState SixCarryPrefixData.program 768 basis 4474 := by
 rfl

theorem frame_4474_769_772 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 772 basis 4474=prefixState SixCarryPrefixData.program 769 basis 4474 := by
 exact at_between SixCarryPrefixData.program 769 772 4474 (by decide +kernel) nw_4474_769_772 basis

theorem frame_4474_773_773 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 773 basis 4474=prefixState SixCarryPrefixData.program 773 basis 4474 := by
 rfl

theorem frame_4474_773_775 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 775 basis 4474=prefixState SixCarryPrefixData.program 773 basis 4474 := by
 exact at_between SixCarryPrefixData.program 773 775 4474 (by decide +kernel) nw_4474_773_775 basis

theorem frame_4474_776_1006 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1006 basis 4474=prefixState SixCarryPrefixData.program 776 basis 4474 := by
 exact at_between SixCarryPrefixData.program 776 1006 4474 (by decide +kernel) nw_4474_776_1006 basis

theorem frame_4474_1008_2143 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2143 basis 4474=prefixState SixCarryPrefixData.program 1008 basis 4474 := by
 exact at_between SixCarryPrefixData.program 1008 2143 4474 (by decide +kernel) nw_4474_1008_2143 basis

theorem frame_4474_2144_2144 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2144 basis 4474=prefixState SixCarryPrefixData.program 2144 basis 4474 := by
 rfl

theorem frame_4474_2145_2148 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2148 basis 4474=prefixState SixCarryPrefixData.program 2145 basis 4474 := by
 exact at_between SixCarryPrefixData.program 2145 2148 4474 (by decide +kernel) nw_4474_2145_2148 basis

theorem frame_4474_2149_2149 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2149 basis 4474=prefixState SixCarryPrefixData.program 2149 basis 4474 := by
 rfl

theorem frame_4475_0_773 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 773 basis 4475=prefixState SixCarryPrefixData.program 0 basis 4475 := by
 exact at_between SixCarryPrefixData.program 0 773 4475 (by decide +kernel) nw_4475_0_773 basis

theorem frame_4475_774_774 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 774 basis 4475=prefixState SixCarryPrefixData.program 774 basis 4475 := by
 rfl

theorem frame_4475_775_778 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 778 basis 4475=prefixState SixCarryPrefixData.program 775 basis 4475 := by
 exact at_between SixCarryPrefixData.program 775 778 4475 (by decide +kernel) nw_4475_775_778 basis

theorem frame_4475_779_779 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 779 basis 4475=prefixState SixCarryPrefixData.program 779 basis 4475 := by
 rfl

theorem frame_4475_779_781 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 781 basis 4475=prefixState SixCarryPrefixData.program 779 basis 4475 := by
 exact at_between SixCarryPrefixData.program 779 781 4475 (by decide +kernel) nw_4475_779_781 basis

theorem frame_4475_782_1003 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1003 basis 4475=prefixState SixCarryPrefixData.program 782 basis 4475 := by
 exact at_between SixCarryPrefixData.program 782 1003 4475 (by decide +kernel) nw_4475_782_1003 basis

theorem frame_4475_1005_2149 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2149 basis 4475=prefixState SixCarryPrefixData.program 1005 basis 4475 := by
 exact at_between SixCarryPrefixData.program 1005 2149 4475 (by decide +kernel) nw_4475_1005_2149 basis

theorem frame_4475_2150_2150 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2150 basis 4475=prefixState SixCarryPrefixData.program 2150 basis 4475 := by
 rfl

theorem frame_4475_2151_2154 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2154 basis 4475=prefixState SixCarryPrefixData.program 2151 basis 4475 := by
 exact at_between SixCarryPrefixData.program 2151 2154 4475 (by decide +kernel) nw_4475_2151_2154 basis

theorem frame_4475_2155_2155 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2155 basis 4475=prefixState SixCarryPrefixData.program 2155 basis 4475 := by
 rfl

theorem frame_4476_0_779 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 779 basis 4476=prefixState SixCarryPrefixData.program 0 basis 4476 := by
 exact at_between SixCarryPrefixData.program 0 779 4476 (by decide +kernel) nw_4476_0_779 basis

theorem frame_4476_780_780 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 780 basis 4476=prefixState SixCarryPrefixData.program 780 basis 4476 := by
 rfl

theorem frame_4476_781_784 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 784 basis 4476=prefixState SixCarryPrefixData.program 781 basis 4476 := by
 exact at_between SixCarryPrefixData.program 781 784 4476 (by decide +kernel) nw_4476_781_784 basis

theorem frame_4476_785_785 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 785 basis 4476=prefixState SixCarryPrefixData.program 785 basis 4476 := by
 rfl

theorem frame_4476_785_787 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 787 basis 4476=prefixState SixCarryPrefixData.program 785 basis 4476 := by
 exact at_between SixCarryPrefixData.program 785 787 4476 (by decide +kernel) nw_4476_785_787 basis

theorem frame_4476_788_1000 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1000 basis 4476=prefixState SixCarryPrefixData.program 788 basis 4476 := by
 exact at_between SixCarryPrefixData.program 788 1000 4476 (by decide +kernel) nw_4476_788_1000 basis

theorem frame_4476_1002_2155 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2155 basis 4476=prefixState SixCarryPrefixData.program 1002 basis 4476 := by
 exact at_between SixCarryPrefixData.program 1002 2155 4476 (by decide +kernel) nw_4476_1002_2155 basis

theorem frame_4476_2156_2156 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2156 basis 4476=prefixState SixCarryPrefixData.program 2156 basis 4476 := by
 rfl

theorem frame_4476_2157_2160 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2160 basis 4476=prefixState SixCarryPrefixData.program 2157 basis 4476 := by
 exact at_between SixCarryPrefixData.program 2157 2160 4476 (by decide +kernel) nw_4476_2157_2160 basis

theorem frame_4476_2161_2161 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2161 basis 4476=prefixState SixCarryPrefixData.program 2161 basis 4476 := by
 rfl

theorem frame_4477_0_785 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 785 basis 4477=prefixState SixCarryPrefixData.program 0 basis 4477 := by
 exact at_between SixCarryPrefixData.program 0 785 4477 (by decide +kernel) nw_4477_0_785 basis

theorem frame_4477_786_786 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 786 basis 4477=prefixState SixCarryPrefixData.program 786 basis 4477 := by
 rfl

theorem frame_4477_787_790 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 790 basis 4477=prefixState SixCarryPrefixData.program 787 basis 4477 := by
 exact at_between SixCarryPrefixData.program 787 790 4477 (by decide +kernel) nw_4477_787_790 basis

theorem frame_4477_791_791 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 791 basis 4477=prefixState SixCarryPrefixData.program 791 basis 4477 := by
 rfl

theorem frame_4477_791_793 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 793 basis 4477=prefixState SixCarryPrefixData.program 791 basis 4477 := by
 exact at_between SixCarryPrefixData.program 791 793 4477 (by decide +kernel) nw_4477_791_793 basis

theorem frame_4477_794_997 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 997 basis 4477=prefixState SixCarryPrefixData.program 794 basis 4477 := by
 exact at_between SixCarryPrefixData.program 794 997 4477 (by decide +kernel) nw_4477_794_997 basis

theorem frame_4477_999_2161 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2161 basis 4477=prefixState SixCarryPrefixData.program 999 basis 4477 := by
 exact at_between SixCarryPrefixData.program 999 2161 4477 (by decide +kernel) nw_4477_999_2161 basis

theorem frame_4477_2162_2162 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2162 basis 4477=prefixState SixCarryPrefixData.program 2162 basis 4477 := by
 rfl

theorem frame_4477_2163_2166 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2166 basis 4477=prefixState SixCarryPrefixData.program 2163 basis 4477 := by
 exact at_between SixCarryPrefixData.program 2163 2166 4477 (by decide +kernel) nw_4477_2163_2166 basis

theorem frame_4477_2167_2167 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2167 basis 4477=prefixState SixCarryPrefixData.program 2167 basis 4477 := by
 rfl

theorem frame_4478_0_791 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 791 basis 4478=prefixState SixCarryPrefixData.program 0 basis 4478 := by
 exact at_between SixCarryPrefixData.program 0 791 4478 (by decide +kernel) nw_4478_0_791 basis

theorem frame_4478_792_792 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 792 basis 4478=prefixState SixCarryPrefixData.program 792 basis 4478 := by
 rfl

theorem frame_4478_793_796 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 796 basis 4478=prefixState SixCarryPrefixData.program 793 basis 4478 := by
 exact at_between SixCarryPrefixData.program 793 796 4478 (by decide +kernel) nw_4478_793_796 basis

theorem frame_4478_797_797 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 797 basis 4478=prefixState SixCarryPrefixData.program 797 basis 4478 := by
 rfl

theorem frame_4478_797_799 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 799 basis 4478=prefixState SixCarryPrefixData.program 797 basis 4478 := by
 exact at_between SixCarryPrefixData.program 797 799 4478 (by decide +kernel) nw_4478_797_799 basis

theorem frame_4478_800_994 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 994 basis 4478=prefixState SixCarryPrefixData.program 800 basis 4478 := by
 exact at_between SixCarryPrefixData.program 800 994 4478 (by decide +kernel) nw_4478_800_994 basis

theorem frame_4478_996_2167 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2167 basis 4478=prefixState SixCarryPrefixData.program 996 basis 4478 := by
 exact at_between SixCarryPrefixData.program 996 2167 4478 (by decide +kernel) nw_4478_996_2167 basis

theorem frame_4478_2168_2168 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2168 basis 4478=prefixState SixCarryPrefixData.program 2168 basis 4478 := by
 rfl

theorem frame_4478_2169_2172 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2172 basis 4478=prefixState SixCarryPrefixData.program 2169 basis 4478 := by
 exact at_between SixCarryPrefixData.program 2169 2172 4478 (by decide +kernel) nw_4478_2169_2172 basis

theorem frame_4478_2173_2173 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2173 basis 4478=prefixState SixCarryPrefixData.program 2173 basis 4478 := by
 rfl

theorem frame_4479_0_797 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 797 basis 4479=prefixState SixCarryPrefixData.program 0 basis 4479 := by
 exact at_between SixCarryPrefixData.program 0 797 4479 (by decide +kernel) nw_4479_0_797 basis

theorem frame_4479_798_798 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 798 basis 4479=prefixState SixCarryPrefixData.program 798 basis 4479 := by
 rfl

theorem frame_4479_799_802 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 802 basis 4479=prefixState SixCarryPrefixData.program 799 basis 4479 := by
 exact at_between SixCarryPrefixData.program 799 802 4479 (by decide +kernel) nw_4479_799_802 basis

theorem frame_4479_803_803 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 803 basis 4479=prefixState SixCarryPrefixData.program 803 basis 4479 := by
 rfl

theorem frame_4479_803_805 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 805 basis 4479=prefixState SixCarryPrefixData.program 803 basis 4479 := by
 exact at_between SixCarryPrefixData.program 803 805 4479 (by decide +kernel) nw_4479_803_805 basis

theorem frame_4479_806_991 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 991 basis 4479=prefixState SixCarryPrefixData.program 806 basis 4479 := by
 exact at_between SixCarryPrefixData.program 806 991 4479 (by decide +kernel) nw_4479_806_991 basis

theorem frame_4479_993_2173 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2173 basis 4479=prefixState SixCarryPrefixData.program 993 basis 4479 := by
 exact at_between SixCarryPrefixData.program 993 2173 4479 (by decide +kernel) nw_4479_993_2173 basis

theorem frame_4479_2174_2174 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2174 basis 4479=prefixState SixCarryPrefixData.program 2174 basis 4479 := by
 rfl

theorem frame_4479_2175_2178 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2178 basis 4479=prefixState SixCarryPrefixData.program 2175 basis 4479 := by
 exact at_between SixCarryPrefixData.program 2175 2178 4479 (by decide +kernel) nw_4479_2175_2178 basis

theorem frame_4479_2179_2179 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2179 basis 4479=prefixState SixCarryPrefixData.program 2179 basis 4479 := by
 rfl

theorem frame_4480_0_803 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 803 basis 4480=prefixState SixCarryPrefixData.program 0 basis 4480 := by
 exact at_between SixCarryPrefixData.program 0 803 4480 (by decide +kernel) nw_4480_0_803 basis

theorem frame_4480_804_804 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 804 basis 4480=prefixState SixCarryPrefixData.program 804 basis 4480 := by
 rfl

theorem frame_4480_805_808 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 808 basis 4480=prefixState SixCarryPrefixData.program 805 basis 4480 := by
 exact at_between SixCarryPrefixData.program 805 808 4480 (by decide +kernel) nw_4480_805_808 basis

theorem frame_4480_809_809 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 809 basis 4480=prefixState SixCarryPrefixData.program 809 basis 4480 := by
 rfl

theorem frame_4480_809_811 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 811 basis 4480=prefixState SixCarryPrefixData.program 809 basis 4480 := by
 exact at_between SixCarryPrefixData.program 809 811 4480 (by decide +kernel) nw_4480_809_811 basis

theorem frame_4480_812_988 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 988 basis 4480=prefixState SixCarryPrefixData.program 812 basis 4480 := by
 exact at_between SixCarryPrefixData.program 812 988 4480 (by decide +kernel) nw_4480_812_988 basis

theorem frame_4480_990_2179 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2179 basis 4480=prefixState SixCarryPrefixData.program 990 basis 4480 := by
 exact at_between SixCarryPrefixData.program 990 2179 4480 (by decide +kernel) nw_4480_990_2179 basis

theorem frame_4480_2180_2180 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2180 basis 4480=prefixState SixCarryPrefixData.program 2180 basis 4480 := by
 rfl

theorem frame_4480_2181_2184 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2184 basis 4480=prefixState SixCarryPrefixData.program 2181 basis 4480 := by
 exact at_between SixCarryPrefixData.program 2181 2184 4480 (by decide +kernel) nw_4480_2181_2184 basis

theorem frame_4480_2185_2185 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2185 basis 4480=prefixState SixCarryPrefixData.program 2185 basis 4480 := by
 rfl

theorem frame_4481_0_809 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 809 basis 4481=prefixState SixCarryPrefixData.program 0 basis 4481 := by
 exact at_between SixCarryPrefixData.program 0 809 4481 (by decide +kernel) nw_4481_0_809 basis

theorem frame_4481_810_810 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 810 basis 4481=prefixState SixCarryPrefixData.program 810 basis 4481 := by
 rfl

theorem frame_4481_811_814 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 814 basis 4481=prefixState SixCarryPrefixData.program 811 basis 4481 := by
 exact at_between SixCarryPrefixData.program 811 814 4481 (by decide +kernel) nw_4481_811_814 basis

theorem frame_4481_815_815 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 815 basis 4481=prefixState SixCarryPrefixData.program 815 basis 4481 := by
 rfl

theorem frame_4481_815_817 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 817 basis 4481=prefixState SixCarryPrefixData.program 815 basis 4481 := by
 exact at_between SixCarryPrefixData.program 815 817 4481 (by decide +kernel) nw_4481_815_817 basis

theorem frame_4481_818_985 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 985 basis 4481=prefixState SixCarryPrefixData.program 818 basis 4481 := by
 exact at_between SixCarryPrefixData.program 818 985 4481 (by decide +kernel) nw_4481_818_985 basis

theorem frame_4481_987_2185 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2185 basis 4481=prefixState SixCarryPrefixData.program 987 basis 4481 := by
 exact at_between SixCarryPrefixData.program 987 2185 4481 (by decide +kernel) nw_4481_987_2185 basis

theorem frame_4481_2186_2186 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2186 basis 4481=prefixState SixCarryPrefixData.program 2186 basis 4481 := by
 rfl

theorem frame_4481_2187_2190 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2190 basis 4481=prefixState SixCarryPrefixData.program 2187 basis 4481 := by
 exact at_between SixCarryPrefixData.program 2187 2190 4481 (by decide +kernel) nw_4481_2187_2190 basis

theorem frame_4481_2191_2191 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2191 basis 4481=prefixState SixCarryPrefixData.program 2191 basis 4481 := by
 rfl

theorem frame_4482_0_815 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 815 basis 4482=prefixState SixCarryPrefixData.program 0 basis 4482 := by
 exact at_between SixCarryPrefixData.program 0 815 4482 (by decide +kernel) nw_4482_0_815 basis

theorem frame_4482_816_816 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 816 basis 4482=prefixState SixCarryPrefixData.program 816 basis 4482 := by
 rfl

theorem frame_4482_817_820 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 820 basis 4482=prefixState SixCarryPrefixData.program 817 basis 4482 := by
 exact at_between SixCarryPrefixData.program 817 820 4482 (by decide +kernel) nw_4482_817_820 basis

theorem frame_4482_821_821 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 821 basis 4482=prefixState SixCarryPrefixData.program 821 basis 4482 := by
 rfl

theorem frame_4482_821_823 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 823 basis 4482=prefixState SixCarryPrefixData.program 821 basis 4482 := by
 exact at_between SixCarryPrefixData.program 821 823 4482 (by decide +kernel) nw_4482_821_823 basis

theorem frame_4482_824_982 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 982 basis 4482=prefixState SixCarryPrefixData.program 824 basis 4482 := by
 exact at_between SixCarryPrefixData.program 824 982 4482 (by decide +kernel) nw_4482_824_982 basis

theorem frame_4482_984_2191 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2191 basis 4482=prefixState SixCarryPrefixData.program 984 basis 4482 := by
 exact at_between SixCarryPrefixData.program 984 2191 4482 (by decide +kernel) nw_4482_984_2191 basis

theorem frame_4482_2192_2192 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2192 basis 4482=prefixState SixCarryPrefixData.program 2192 basis 4482 := by
 rfl

theorem frame_4482_2193_2196 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2196 basis 4482=prefixState SixCarryPrefixData.program 2193 basis 4482 := by
 exact at_between SixCarryPrefixData.program 2193 2196 4482 (by decide +kernel) nw_4482_2193_2196 basis

theorem frame_4482_2197_2197 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2197 basis 4482=prefixState SixCarryPrefixData.program 2197 basis 4482 := by
 rfl

theorem frame_4483_0_821 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 821 basis 4483=prefixState SixCarryPrefixData.program 0 basis 4483 := by
 exact at_between SixCarryPrefixData.program 0 821 4483 (by decide +kernel) nw_4483_0_821 basis

theorem frame_4483_822_822 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 822 basis 4483=prefixState SixCarryPrefixData.program 822 basis 4483 := by
 rfl

theorem frame_4483_823_826 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 826 basis 4483=prefixState SixCarryPrefixData.program 823 basis 4483 := by
 exact at_between SixCarryPrefixData.program 823 826 4483 (by decide +kernel) nw_4483_823_826 basis

theorem frame_4483_827_827 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 827 basis 4483=prefixState SixCarryPrefixData.program 827 basis 4483 := by
 rfl

theorem frame_4483_827_829 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 829 basis 4483=prefixState SixCarryPrefixData.program 827 basis 4483 := by
 exact at_between SixCarryPrefixData.program 827 829 4483 (by decide +kernel) nw_4483_827_829 basis

theorem frame_4483_830_979 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 979 basis 4483=prefixState SixCarryPrefixData.program 830 basis 4483 := by
 exact at_between SixCarryPrefixData.program 830 979 4483 (by decide +kernel) nw_4483_830_979 basis

theorem frame_4483_981_2197 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2197 basis 4483=prefixState SixCarryPrefixData.program 981 basis 4483 := by
 exact at_between SixCarryPrefixData.program 981 2197 4483 (by decide +kernel) nw_4483_981_2197 basis

theorem frame_4483_2198_2198 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2198 basis 4483=prefixState SixCarryPrefixData.program 2198 basis 4483 := by
 rfl

theorem frame_4483_2199_2202 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2202 basis 4483=prefixState SixCarryPrefixData.program 2199 basis 4483 := by
 exact at_between SixCarryPrefixData.program 2199 2202 4483 (by decide +kernel) nw_4483_2199_2202 basis

theorem frame_4483_2203_2203 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2203 basis 4483=prefixState SixCarryPrefixData.program 2203 basis 4483 := by
 rfl

theorem frame_4484_0_827 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 827 basis 4484=prefixState SixCarryPrefixData.program 0 basis 4484 := by
 exact at_between SixCarryPrefixData.program 0 827 4484 (by decide +kernel) nw_4484_0_827 basis

theorem frame_4484_828_828 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 828 basis 4484=prefixState SixCarryPrefixData.program 828 basis 4484 := by
 rfl

theorem frame_4484_829_832 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 832 basis 4484=prefixState SixCarryPrefixData.program 829 basis 4484 := by
 exact at_between SixCarryPrefixData.program 829 832 4484 (by decide +kernel) nw_4484_829_832 basis

theorem frame_4484_833_833 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 833 basis 4484=prefixState SixCarryPrefixData.program 833 basis 4484 := by
 rfl

theorem frame_4484_833_835 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 835 basis 4484=prefixState SixCarryPrefixData.program 833 basis 4484 := by
 exact at_between SixCarryPrefixData.program 833 835 4484 (by decide +kernel) nw_4484_833_835 basis

theorem frame_4484_836_976 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 976 basis 4484=prefixState SixCarryPrefixData.program 836 basis 4484 := by
 exact at_between SixCarryPrefixData.program 836 976 4484 (by decide +kernel) nw_4484_836_976 basis

theorem frame_4484_978_2203 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2203 basis 4484=prefixState SixCarryPrefixData.program 978 basis 4484 := by
 exact at_between SixCarryPrefixData.program 978 2203 4484 (by decide +kernel) nw_4484_978_2203 basis

theorem frame_4484_2204_2204 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2204 basis 4484=prefixState SixCarryPrefixData.program 2204 basis 4484 := by
 rfl

theorem frame_4484_2205_2208 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2208 basis 4484=prefixState SixCarryPrefixData.program 2205 basis 4484 := by
 exact at_between SixCarryPrefixData.program 2205 2208 4484 (by decide +kernel) nw_4484_2205_2208 basis

theorem frame_4484_2209_2209 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2209 basis 4484=prefixState SixCarryPrefixData.program 2209 basis 4484 := by
 rfl

theorem frame_4485_0_833 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 833 basis 4485=prefixState SixCarryPrefixData.program 0 basis 4485 := by
 exact at_between SixCarryPrefixData.program 0 833 4485 (by decide +kernel) nw_4485_0_833 basis

theorem frame_4485_834_834 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 834 basis 4485=prefixState SixCarryPrefixData.program 834 basis 4485 := by
 rfl

theorem frame_4485_835_838 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 838 basis 4485=prefixState SixCarryPrefixData.program 835 basis 4485 := by
 exact at_between SixCarryPrefixData.program 835 838 4485 (by decide +kernel) nw_4485_835_838 basis

theorem frame_4485_839_839 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 839 basis 4485=prefixState SixCarryPrefixData.program 839 basis 4485 := by
 rfl

theorem frame_4485_839_841 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 841 basis 4485=prefixState SixCarryPrefixData.program 839 basis 4485 := by
 exact at_between SixCarryPrefixData.program 839 841 4485 (by decide +kernel) nw_4485_839_841 basis

theorem frame_4485_842_973 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 973 basis 4485=prefixState SixCarryPrefixData.program 842 basis 4485 := by
 exact at_between SixCarryPrefixData.program 842 973 4485 (by decide +kernel) nw_4485_842_973 basis

theorem frame_4485_975_2209 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2209 basis 4485=prefixState SixCarryPrefixData.program 975 basis 4485 := by
 exact at_between SixCarryPrefixData.program 975 2209 4485 (by decide +kernel) nw_4485_975_2209 basis

theorem frame_4485_2210_2210 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2210 basis 4485=prefixState SixCarryPrefixData.program 2210 basis 4485 := by
 rfl

theorem frame_4485_2211_2214 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2214 basis 4485=prefixState SixCarryPrefixData.program 2211 basis 4485 := by
 exact at_between SixCarryPrefixData.program 2211 2214 4485 (by decide +kernel) nw_4485_2211_2214 basis

theorem frame_4485_2215_2215 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2215 basis 4485=prefixState SixCarryPrefixData.program 2215 basis 4485 := by
 rfl

theorem frame_4486_0_839 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 839 basis 4486=prefixState SixCarryPrefixData.program 0 basis 4486 := by
 exact at_between SixCarryPrefixData.program 0 839 4486 (by decide +kernel) nw_4486_0_839 basis

theorem frame_4486_840_840 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 840 basis 4486=prefixState SixCarryPrefixData.program 840 basis 4486 := by
 rfl

theorem frame_4486_841_844 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 844 basis 4486=prefixState SixCarryPrefixData.program 841 basis 4486 := by
 exact at_between SixCarryPrefixData.program 841 844 4486 (by decide +kernel) nw_4486_841_844 basis

theorem frame_4486_845_845 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 845 basis 4486=prefixState SixCarryPrefixData.program 845 basis 4486 := by
 rfl

theorem frame_4486_845_847 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 847 basis 4486=prefixState SixCarryPrefixData.program 845 basis 4486 := by
 exact at_between SixCarryPrefixData.program 845 847 4486 (by decide +kernel) nw_4486_845_847 basis

theorem frame_4486_848_970 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 970 basis 4486=prefixState SixCarryPrefixData.program 848 basis 4486 := by
 exact at_between SixCarryPrefixData.program 848 970 4486 (by decide +kernel) nw_4486_848_970 basis

theorem frame_4486_972_2215 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2215 basis 4486=prefixState SixCarryPrefixData.program 972 basis 4486 := by
 exact at_between SixCarryPrefixData.program 972 2215 4486 (by decide +kernel) nw_4486_972_2215 basis

theorem frame_4486_2216_2216 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2216 basis 4486=prefixState SixCarryPrefixData.program 2216 basis 4486 := by
 rfl

theorem frame_4486_2217_2220 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2220 basis 4486=prefixState SixCarryPrefixData.program 2217 basis 4486 := by
 exact at_between SixCarryPrefixData.program 2217 2220 4486 (by decide +kernel) nw_4486_2217_2220 basis

theorem frame_4486_2221_2221 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2221 basis 4486=prefixState SixCarryPrefixData.program 2221 basis 4486 := by
 rfl

theorem frame_4487_0_845 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 845 basis 4487=prefixState SixCarryPrefixData.program 0 basis 4487 := by
 exact at_between SixCarryPrefixData.program 0 845 4487 (by decide +kernel) nw_4487_0_845 basis

theorem frame_4487_846_846 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 846 basis 4487=prefixState SixCarryPrefixData.program 846 basis 4487 := by
 rfl

theorem frame_4487_847_850 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 850 basis 4487=prefixState SixCarryPrefixData.program 847 basis 4487 := by
 exact at_between SixCarryPrefixData.program 847 850 4487 (by decide +kernel) nw_4487_847_850 basis

theorem frame_4487_851_851 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 851 basis 4487=prefixState SixCarryPrefixData.program 851 basis 4487 := by
 rfl

theorem frame_4487_851_853 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 853 basis 4487=prefixState SixCarryPrefixData.program 851 basis 4487 := by
 exact at_between SixCarryPrefixData.program 851 853 4487 (by decide +kernel) nw_4487_851_853 basis

theorem frame_4487_854_967 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 967 basis 4487=prefixState SixCarryPrefixData.program 854 basis 4487 := by
 exact at_between SixCarryPrefixData.program 854 967 4487 (by decide +kernel) nw_4487_854_967 basis

theorem frame_4487_969_2221 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2221 basis 4487=prefixState SixCarryPrefixData.program 969 basis 4487 := by
 exact at_between SixCarryPrefixData.program 969 2221 4487 (by decide +kernel) nw_4487_969_2221 basis

theorem frame_4487_2222_2222 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2222 basis 4487=prefixState SixCarryPrefixData.program 2222 basis 4487 := by
 rfl

theorem frame_4487_2223_2226 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2226 basis 4487=prefixState SixCarryPrefixData.program 2223 basis 4487 := by
 exact at_between SixCarryPrefixData.program 2223 2226 4487 (by decide +kernel) nw_4487_2223_2226 basis

theorem frame_4487_2227_2227 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2227 basis 4487=prefixState SixCarryPrefixData.program 2227 basis 4487 := by
 rfl

theorem frame_4488_0_851 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 851 basis 4488=prefixState SixCarryPrefixData.program 0 basis 4488 := by
 exact at_between SixCarryPrefixData.program 0 851 4488 (by decide +kernel) nw_4488_0_851 basis

theorem frame_4488_852_852 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 852 basis 4488=prefixState SixCarryPrefixData.program 852 basis 4488 := by
 rfl

theorem frame_4488_853_856 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 856 basis 4488=prefixState SixCarryPrefixData.program 853 basis 4488 := by
 exact at_between SixCarryPrefixData.program 853 856 4488 (by decide +kernel) nw_4488_853_856 basis

theorem frame_4488_966_2227 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2227 basis 4488=prefixState SixCarryPrefixData.program 966 basis 4488 := by
 exact at_between SixCarryPrefixData.program 966 2227 4488 (by decide +kernel) nw_4488_966_2227 basis

theorem frame_4488_2228_2228 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2228 basis 4488=prefixState SixCarryPrefixData.program 2228 basis 4488 := by
 rfl

theorem frame_4488_2229_2232 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2232 basis 4488=prefixState SixCarryPrefixData.program 2229 basis 4488 := by
 exact at_between SixCarryPrefixData.program 2229 2232 4488 (by decide +kernel) nw_4488_2229_2232 basis

theorem frame_4488_2233_2233 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2233 basis 4488=prefixState SixCarryPrefixData.program 2233 basis 4488 := by
 rfl

theorem frame_4489_963_2233 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2233 basis 4489=prefixState SixCarryPrefixData.program 963 basis 4489 := by
 exact at_between SixCarryPrefixData.program 963 2233 4489 (by decide +kernel) nw_4489_963_2233 basis

theorem frame_4489_2234_2234 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2234 basis 4489=prefixState SixCarryPrefixData.program 2234 basis 4489 := by
 rfl

theorem frame_4489_2235_2238 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2238 basis 4489=prefixState SixCarryPrefixData.program 2235 basis 4489 := by
 exact at_between SixCarryPrefixData.program 2235 2238 4489 (by decide +kernel) nw_4489_2235_2238 basis

theorem frame_4489_2239_2239 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2239 basis 4489=prefixState SixCarryPrefixData.program 2239 basis 4489 := by
 rfl

theorem frame_4490_960_2239 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2239 basis 4490=prefixState SixCarryPrefixData.program 960 basis 4490 := by
 exact at_between SixCarryPrefixData.program 960 2239 4490 (by decide +kernel) nw_4490_960_2239 basis

theorem frame_4490_2240_2240 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2240 basis 4490=prefixState SixCarryPrefixData.program 2240 basis 4490 := by
 rfl

theorem frame_4490_2241_2244 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2244 basis 4490=prefixState SixCarryPrefixData.program 2241 basis 4490 := by
 exact at_between SixCarryPrefixData.program 2241 2244 4490 (by decide +kernel) nw_4490_2241_2244 basis

theorem frame_4490_2245_2245 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2245 basis 4490=prefixState SixCarryPrefixData.program 2245 basis 4490 := by
 rfl

theorem frame_4491_957_2245 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2245 basis 4491=prefixState SixCarryPrefixData.program 957 basis 4491 := by
 exact at_between SixCarryPrefixData.program 957 2245 4491 (by decide +kernel) nw_4491_957_2245 basis

theorem frame_4491_2246_2246 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2246 basis 4491=prefixState SixCarryPrefixData.program 2246 basis 4491 := by
 rfl

theorem frame_4491_2247_2250 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2250 basis 4491=prefixState SixCarryPrefixData.program 2247 basis 4491 := by
 exact at_between SixCarryPrefixData.program 2247 2250 4491 (by decide +kernel) nw_4491_2247_2250 basis

theorem frame_4491_2251_2251 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2251 basis 4491=prefixState SixCarryPrefixData.program 2251 basis 4491 := by
 rfl

theorem frame_4492_954_2251 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2251 basis 4492=prefixState SixCarryPrefixData.program 954 basis 4492 := by
 exact at_between SixCarryPrefixData.program 954 2251 4492 (by decide +kernel) nw_4492_954_2251 basis

theorem frame_4492_2252_2252 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2252 basis 4492=prefixState SixCarryPrefixData.program 2252 basis 4492 := by
 rfl

theorem frame_4492_2253_2256 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2256 basis 4492=prefixState SixCarryPrefixData.program 2253 basis 4492 := by
 exact at_between SixCarryPrefixData.program 2253 2256 4492 (by decide +kernel) nw_4492_2253_2256 basis

theorem frame_4607_0_102 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 102 basis 4607=prefixState SixCarryPrefixData.program 0 basis 4607 := by
 exact at_between SixCarryPrefixData.program 0 102 4607 (by decide +kernel) nw_4607_0_102 basis

theorem frame_4607_103_735 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 735 basis 4607=prefixState SixCarryPrefixData.program 103 basis 4607 := by
 exact at_between SixCarryPrefixData.program 103 735 4607 (by decide +kernel) nw_4607_103_735 basis

theorem frame_4607_736_737 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 737 basis 4607=prefixState SixCarryPrefixData.program 736 basis 4607 := by
 exact at_between SixCarryPrefixData.program 736 737 4607 (by decide +kernel) nw_4607_736_737 basis

theorem frame_4608_0_103 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 103 basis 4608=prefixState SixCarryPrefixData.program 0 basis 4608 := by
 exact at_between SixCarryPrefixData.program 0 103 4608 (by decide +kernel) nw_4608_0_103 basis

theorem frame_4608_104_741 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 741 basis 4608=prefixState SixCarryPrefixData.program 104 basis 4608 := by
 exact at_between SixCarryPrefixData.program 104 741 4608 (by decide +kernel) nw_4608_104_741 basis

theorem frame_4608_742_743 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 743 basis 4608=prefixState SixCarryPrefixData.program 742 basis 4608 := by
 exact at_between SixCarryPrefixData.program 742 743 4608 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 742 746 743 4608 (by decide +kernel) nw_4608_742_746) basis

theorem frame_4608_742_746 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 746 basis 4608=prefixState SixCarryPrefixData.program 742 basis 4608 := by
 exact at_between SixCarryPrefixData.program 742 746 4608 (by decide +kernel) nw_4608_742_746 basis

theorem frame_4608_747_1020 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1020 basis 4608=prefixState SixCarryPrefixData.program 747 basis 4608 := by
 exact at_between SixCarryPrefixData.program 747 1020 4608 (by decide +kernel) nw_4608_747_1020 basis

theorem frame_4608_1021_1021 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1021 basis 4608=prefixState SixCarryPrefixData.program 1021 basis 4608 := by
 rfl

theorem frame_4608_1022_1414 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1414 basis 4608=prefixState SixCarryPrefixData.program 1022 basis 4608 := by
 exact at_between SixCarryPrefixData.program 1022 1414 4608 (by decide +kernel) nw_4608_1022_1414 basis

theorem frame_4608_1415_2141 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2141 basis 4608=prefixState SixCarryPrefixData.program 1415 basis 4608 := by
 exact at_between SixCarryPrefixData.program 1415 2141 4608 (by decide +kernel) nw_4608_1415_2141 basis

theorem frame_4608_2142_2143 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2143 basis 4608=prefixState SixCarryPrefixData.program 2142 basis 4608 := by
 exact at_between SixCarryPrefixData.program 2142 2143 4608 (by decide +kernel) nw_4608_2142_2143 basis

theorem frame_4609_0_104 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 104 basis 4609=prefixState SixCarryPrefixData.program 0 basis 4609 := by
 exact at_between SixCarryPrefixData.program 0 104 4609 (by decide +kernel) nw_4609_0_104 basis

theorem frame_4609_105_747 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 747 basis 4609=prefixState SixCarryPrefixData.program 105 basis 4609 := by
 exact at_between SixCarryPrefixData.program 105 747 4609 (by decide +kernel) nw_4609_105_747 basis

theorem frame_4609_748_752 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 752 basis 4609=prefixState SixCarryPrefixData.program 748 basis 4609 := by
 exact at_between SixCarryPrefixData.program 748 752 4609 (by decide +kernel) nw_4609_748_752 basis

theorem frame_4609_753_1017 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1017 basis 4609=prefixState SixCarryPrefixData.program 753 basis 4609 := by
 exact at_between SixCarryPrefixData.program 753 1017 4609 (by decide +kernel) nw_4609_753_1017 basis

theorem frame_4609_1018_1018 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1018 basis 4609=prefixState SixCarryPrefixData.program 1018 basis 4609 := by
 rfl

theorem frame_4609_1019_1415 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1415 basis 4609=prefixState SixCarryPrefixData.program 1019 basis 4609 := by
 exact at_between SixCarryPrefixData.program 1019 1415 4609 (by decide +kernel) nw_4609_1019_1415 basis

theorem frame_4609_1416_2147 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2147 basis 4609=prefixState SixCarryPrefixData.program 1416 basis 4609 := by
 exact at_between SixCarryPrefixData.program 1416 2147 4609 (by decide +kernel) nw_4609_1416_2147 basis

theorem frame_4609_2148_2149 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2149 basis 4609=prefixState SixCarryPrefixData.program 2148 basis 4609 := by
 exact at_between SixCarryPrefixData.program 2148 2149 4609 (by decide +kernel) nw_4609_2148_2149 basis

theorem frame_4610_2154_2155 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2155 basis 4610=prefixState SixCarryPrefixData.program 2154 basis 4610 := by
 exact at_between SixCarryPrefixData.program 2154 2155 4610 (by decide +kernel) nw_4610_2154_2155 basis

theorem frame_4611_2160_2161 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2161 basis 4611=prefixState SixCarryPrefixData.program 2160 basis 4611 := by
 exact at_between SixCarryPrefixData.program 2160 2161 4611 (by decide +kernel) nw_4611_2160_2161 basis

theorem frame_4612_766_767 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 767 basis 4612=prefixState SixCarryPrefixData.program 766 basis 4612 := by
 exact at_between SixCarryPrefixData.program 766 767 4612 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 766 770 767 4612 (by decide +kernel) nw_4612_766_770) basis

theorem frame_4612_766_770 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 770 basis 4612=prefixState SixCarryPrefixData.program 766 basis 4612 := by
 exact at_between SixCarryPrefixData.program 766 770 4612 (by decide +kernel) nw_4612_766_770 basis

theorem frame_4612_771_1008 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1008 basis 4612=prefixState SixCarryPrefixData.program 771 basis 4612 := by
 exact at_between SixCarryPrefixData.program 771 1008 4612 (by decide +kernel) nw_4612_771_1008 basis

theorem frame_4612_1009_1009 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1009 basis 4612=prefixState SixCarryPrefixData.program 1009 basis 4612 := by
 rfl

theorem frame_4612_1010_1418 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1418 basis 4612=prefixState SixCarryPrefixData.program 1010 basis 4612 := by
 exact at_between SixCarryPrefixData.program 1010 1418 4612 (by decide +kernel) nw_4612_1010_1418 basis

theorem frame_4612_1419_2165 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2165 basis 4612=prefixState SixCarryPrefixData.program 1419 basis 4612 := by
 exact at_between SixCarryPrefixData.program 1419 2165 4612 (by decide +kernel) nw_4612_1419_2165 basis

theorem frame_4612_2166_2167 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2167 basis 4612=prefixState SixCarryPrefixData.program 2166 basis 4612 := by
 exact at_between SixCarryPrefixData.program 2166 2167 4612 (by decide +kernel) nw_4612_2166_2167 basis

theorem frame_4613_0_108 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 108 basis 4613=prefixState SixCarryPrefixData.program 0 basis 4613 := by
 exact at_between SixCarryPrefixData.program 0 108 4613 (by decide +kernel) nw_4613_0_108 basis

theorem frame_4613_109_771 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 771 basis 4613=prefixState SixCarryPrefixData.program 109 basis 4613 := by
 exact at_between SixCarryPrefixData.program 109 771 4613 (by decide +kernel) nw_4613_109_771 basis

theorem frame_4613_772_773 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 773 basis 4613=prefixState SixCarryPrefixData.program 772 basis 4613 := by
 exact at_between SixCarryPrefixData.program 772 773 4613 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 772 776 773 4613 (by decide +kernel) nw_4613_772_776) basis

theorem frame_4613_772_776 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 776 basis 4613=prefixState SixCarryPrefixData.program 772 basis 4613 := by
 exact at_between SixCarryPrefixData.program 772 776 4613 (by decide +kernel) nw_4613_772_776 basis

theorem frame_4613_777_1005 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1005 basis 4613=prefixState SixCarryPrefixData.program 777 basis 4613 := by
 exact at_between SixCarryPrefixData.program 777 1005 4613 (by decide +kernel) nw_4613_777_1005 basis

theorem frame_4613_1006_1006 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1006 basis 4613=prefixState SixCarryPrefixData.program 1006 basis 4613 := by
 rfl

theorem frame_4613_1007_1419 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1419 basis 4613=prefixState SixCarryPrefixData.program 1007 basis 4613 := by
 exact at_between SixCarryPrefixData.program 1007 1419 4613 (by decide +kernel) nw_4613_1007_1419 basis

theorem frame_4613_1420_2171 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2171 basis 4613=prefixState SixCarryPrefixData.program 1420 basis 4613 := by
 exact at_between SixCarryPrefixData.program 1420 2171 4613 (by decide +kernel) nw_4613_1420_2171 basis

theorem frame_4613_2172_2173 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2173 basis 4613=prefixState SixCarryPrefixData.program 2172 basis 4613 := by
 exact at_between SixCarryPrefixData.program 2172 2173 4613 (by decide +kernel) nw_4613_2172_2173 basis

theorem frame_4614_0_109 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 109 basis 4614=prefixState SixCarryPrefixData.program 0 basis 4614 := by
 exact at_between SixCarryPrefixData.program 0 109 4614 (by decide +kernel) nw_4614_0_109 basis

theorem frame_4614_110_777 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 777 basis 4614=prefixState SixCarryPrefixData.program 110 basis 4614 := by
 exact at_between SixCarryPrefixData.program 110 777 4614 (by decide +kernel) nw_4614_110_777 basis

theorem frame_4614_778_779 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 779 basis 4614=prefixState SixCarryPrefixData.program 778 basis 4614 := by
 exact at_between SixCarryPrefixData.program 778 779 4614 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 778 782 779 4614 (by decide +kernel) nw_4614_778_782) basis

theorem frame_4614_778_782 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 782 basis 4614=prefixState SixCarryPrefixData.program 778 basis 4614 := by
 exact at_between SixCarryPrefixData.program 778 782 4614 (by decide +kernel) nw_4614_778_782 basis

theorem frame_4614_783_1002 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1002 basis 4614=prefixState SixCarryPrefixData.program 783 basis 4614 := by
 exact at_between SixCarryPrefixData.program 783 1002 4614 (by decide +kernel) nw_4614_783_1002 basis

theorem frame_4614_1003_1003 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1003 basis 4614=prefixState SixCarryPrefixData.program 1003 basis 4614 := by
 rfl

theorem frame_4614_1004_1420 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1420 basis 4614=prefixState SixCarryPrefixData.program 1004 basis 4614 := by
 exact at_between SixCarryPrefixData.program 1004 1420 4614 (by decide +kernel) nw_4614_1004_1420 basis

theorem frame_4614_1421_2177 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2177 basis 4614=prefixState SixCarryPrefixData.program 1421 basis 4614 := by
 exact at_between SixCarryPrefixData.program 1421 2177 4614 (by decide +kernel) nw_4614_1421_2177 basis

theorem frame_4614_2178_2179 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2179 basis 4614=prefixState SixCarryPrefixData.program 2178 basis 4614 := by
 exact at_between SixCarryPrefixData.program 2178 2179 4614 (by decide +kernel) nw_4614_2178_2179 basis

theorem frame_4615_0_110 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 110 basis 4615=prefixState SixCarryPrefixData.program 0 basis 4615 := by
 exact at_between SixCarryPrefixData.program 0 110 4615 (by decide +kernel) nw_4615_0_110 basis

theorem frame_4615_111_783 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 783 basis 4615=prefixState SixCarryPrefixData.program 111 basis 4615 := by
 exact at_between SixCarryPrefixData.program 111 783 4615 (by decide +kernel) nw_4615_111_783 basis

theorem frame_4615_784_785 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 785 basis 4615=prefixState SixCarryPrefixData.program 784 basis 4615 := by
 exact at_between SixCarryPrefixData.program 784 785 4615 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 784 788 785 4615 (by decide +kernel) nw_4615_784_788) basis

theorem frame_4615_784_788 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 788 basis 4615=prefixState SixCarryPrefixData.program 784 basis 4615 := by
 exact at_between SixCarryPrefixData.program 784 788 4615 (by decide +kernel) nw_4615_784_788 basis

theorem frame_4615_789_999 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 999 basis 4615=prefixState SixCarryPrefixData.program 789 basis 4615 := by
 exact at_between SixCarryPrefixData.program 789 999 4615 (by decide +kernel) nw_4615_789_999 basis

theorem frame_4615_1000_1000 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1000 basis 4615=prefixState SixCarryPrefixData.program 1000 basis 4615 := by
 rfl

theorem frame_4615_1001_1421 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1421 basis 4615=prefixState SixCarryPrefixData.program 1001 basis 4615 := by
 exact at_between SixCarryPrefixData.program 1001 1421 4615 (by decide +kernel) nw_4615_1001_1421 basis

theorem frame_4615_1422_2183 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2183 basis 4615=prefixState SixCarryPrefixData.program 1422 basis 4615 := by
 exact at_between SixCarryPrefixData.program 1422 2183 4615 (by decide +kernel) nw_4615_1422_2183 basis

theorem frame_4615_2184_2185 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2185 basis 4615=prefixState SixCarryPrefixData.program 2184 basis 4615 := by
 exact at_between SixCarryPrefixData.program 2184 2185 4615 (by decide +kernel) nw_4615_2184_2185 basis

theorem frame_4616_0_111 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 111 basis 4616=prefixState SixCarryPrefixData.program 0 basis 4616 := by
 exact at_between SixCarryPrefixData.program 0 111 4616 (by decide +kernel) nw_4616_0_111 basis

theorem frame_4616_112_789 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 789 basis 4616=prefixState SixCarryPrefixData.program 112 basis 4616 := by
 exact at_between SixCarryPrefixData.program 112 789 4616 (by decide +kernel) nw_4616_112_789 basis

theorem frame_4616_790_791 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 791 basis 4616=prefixState SixCarryPrefixData.program 790 basis 4616 := by
 exact at_between SixCarryPrefixData.program 790 791 4616 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 790 794 791 4616 (by decide +kernel) nw_4616_790_794) basis

theorem frame_4616_790_794 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 794 basis 4616=prefixState SixCarryPrefixData.program 790 basis 4616 := by
 exact at_between SixCarryPrefixData.program 790 794 4616 (by decide +kernel) nw_4616_790_794 basis

theorem frame_4616_795_996 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 996 basis 4616=prefixState SixCarryPrefixData.program 795 basis 4616 := by
 exact at_between SixCarryPrefixData.program 795 996 4616 (by decide +kernel) nw_4616_795_996 basis

theorem frame_4616_997_997 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 997 basis 4616=prefixState SixCarryPrefixData.program 997 basis 4616 := by
 rfl

theorem frame_4616_998_1422 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1422 basis 4616=prefixState SixCarryPrefixData.program 998 basis 4616 := by
 exact at_between SixCarryPrefixData.program 998 1422 4616 (by decide +kernel) nw_4616_998_1422 basis

theorem frame_4616_1423_2189 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2189 basis 4616=prefixState SixCarryPrefixData.program 1423 basis 4616 := by
 exact at_between SixCarryPrefixData.program 1423 2189 4616 (by decide +kernel) nw_4616_1423_2189 basis

theorem frame_4616_2190_2191 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2191 basis 4616=prefixState SixCarryPrefixData.program 2190 basis 4616 := by
 exact at_between SixCarryPrefixData.program 2190 2191 4616 (by decide +kernel) nw_4616_2190_2191 basis

theorem frame_4617_0_112 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 112 basis 4617=prefixState SixCarryPrefixData.program 0 basis 4617 := by
 exact at_between SixCarryPrefixData.program 0 112 4617 (by decide +kernel) nw_4617_0_112 basis

theorem frame_4617_113_795 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 795 basis 4617=prefixState SixCarryPrefixData.program 113 basis 4617 := by
 exact at_between SixCarryPrefixData.program 113 795 4617 (by decide +kernel) nw_4617_113_795 basis

theorem frame_4617_796_797 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 797 basis 4617=prefixState SixCarryPrefixData.program 796 basis 4617 := by
 exact at_between SixCarryPrefixData.program 796 797 4617 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 796 800 797 4617 (by decide +kernel) nw_4617_796_800) basis

theorem frame_4617_796_800 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 800 basis 4617=prefixState SixCarryPrefixData.program 796 basis 4617 := by
 exact at_between SixCarryPrefixData.program 796 800 4617 (by decide +kernel) nw_4617_796_800 basis

theorem frame_4617_801_993 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 993 basis 4617=prefixState SixCarryPrefixData.program 801 basis 4617 := by
 exact at_between SixCarryPrefixData.program 801 993 4617 (by decide +kernel) nw_4617_801_993 basis

theorem frame_4617_994_994 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 994 basis 4617=prefixState SixCarryPrefixData.program 994 basis 4617 := by
 rfl

theorem frame_4617_995_1423 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1423 basis 4617=prefixState SixCarryPrefixData.program 995 basis 4617 := by
 exact at_between SixCarryPrefixData.program 995 1423 4617 (by decide +kernel) nw_4617_995_1423 basis

theorem frame_4617_1424_2195 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2195 basis 4617=prefixState SixCarryPrefixData.program 1424 basis 4617 := by
 exact at_between SixCarryPrefixData.program 1424 2195 4617 (by decide +kernel) nw_4617_1424_2195 basis

theorem frame_4617_2196_2197 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2197 basis 4617=prefixState SixCarryPrefixData.program 2196 basis 4617 := by
 exact at_between SixCarryPrefixData.program 2196 2197 4617 (by decide +kernel) nw_4617_2196_2197 basis

theorem frame_4618_0_113 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 113 basis 4618=prefixState SixCarryPrefixData.program 0 basis 4618 := by
 exact at_between SixCarryPrefixData.program 0 113 4618 (by decide +kernel) nw_4618_0_113 basis

theorem frame_4618_114_801 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 801 basis 4618=prefixState SixCarryPrefixData.program 114 basis 4618 := by
 exact at_between SixCarryPrefixData.program 114 801 4618 (by decide +kernel) nw_4618_114_801 basis

theorem frame_4618_802_803 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 803 basis 4618=prefixState SixCarryPrefixData.program 802 basis 4618 := by
 exact at_between SixCarryPrefixData.program 802 803 4618 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 802 806 803 4618 (by decide +kernel) nw_4618_802_806) basis

theorem frame_4618_802_806 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 806 basis 4618=prefixState SixCarryPrefixData.program 802 basis 4618 := by
 exact at_between SixCarryPrefixData.program 802 806 4618 (by decide +kernel) nw_4618_802_806 basis

theorem frame_4618_807_990 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 990 basis 4618=prefixState SixCarryPrefixData.program 807 basis 4618 := by
 exact at_between SixCarryPrefixData.program 807 990 4618 (by decide +kernel) nw_4618_807_990 basis

theorem frame_4618_991_991 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 991 basis 4618=prefixState SixCarryPrefixData.program 991 basis 4618 := by
 rfl

theorem frame_4618_992_1424 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1424 basis 4618=prefixState SixCarryPrefixData.program 992 basis 4618 := by
 exact at_between SixCarryPrefixData.program 992 1424 4618 (by decide +kernel) nw_4618_992_1424 basis

theorem frame_4618_1425_2201 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2201 basis 4618=prefixState SixCarryPrefixData.program 1425 basis 4618 := by
 exact at_between SixCarryPrefixData.program 1425 2201 4618 (by decide +kernel) nw_4618_1425_2201 basis

theorem frame_4618_2202_2203 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2203 basis 4618=prefixState SixCarryPrefixData.program 2202 basis 4618 := by
 exact at_between SixCarryPrefixData.program 2202 2203 4618 (by decide +kernel) nw_4618_2202_2203 basis

theorem frame_4619_0_114 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 114 basis 4619=prefixState SixCarryPrefixData.program 0 basis 4619 := by
 exact at_between SixCarryPrefixData.program 0 114 4619 (by decide +kernel) nw_4619_0_114 basis

theorem frame_4619_115_807 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 807 basis 4619=prefixState SixCarryPrefixData.program 115 basis 4619 := by
 exact at_between SixCarryPrefixData.program 115 807 4619 (by decide +kernel) nw_4619_115_807 basis

theorem frame_4619_808_809 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 809 basis 4619=prefixState SixCarryPrefixData.program 808 basis 4619 := by
 exact at_between SixCarryPrefixData.program 808 809 4619 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 808 812 809 4619 (by decide +kernel) nw_4619_808_812) basis

theorem frame_4619_808_812 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 812 basis 4619=prefixState SixCarryPrefixData.program 808 basis 4619 := by
 exact at_between SixCarryPrefixData.program 808 812 4619 (by decide +kernel) nw_4619_808_812 basis

theorem frame_4619_813_987 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 987 basis 4619=prefixState SixCarryPrefixData.program 813 basis 4619 := by
 exact at_between SixCarryPrefixData.program 813 987 4619 (by decide +kernel) nw_4619_813_987 basis

theorem frame_4619_988_988 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 988 basis 4619=prefixState SixCarryPrefixData.program 988 basis 4619 := by
 rfl

theorem frame_4619_989_1425 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1425 basis 4619=prefixState SixCarryPrefixData.program 989 basis 4619 := by
 exact at_between SixCarryPrefixData.program 989 1425 4619 (by decide +kernel) nw_4619_989_1425 basis

theorem frame_4619_1426_2207 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2207 basis 4619=prefixState SixCarryPrefixData.program 1426 basis 4619 := by
 exact at_between SixCarryPrefixData.program 1426 2207 4619 (by decide +kernel) nw_4619_1426_2207 basis

theorem frame_4619_2208_2209 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2209 basis 4619=prefixState SixCarryPrefixData.program 2208 basis 4619 := by
 exact at_between SixCarryPrefixData.program 2208 2209 4619 (by decide +kernel) nw_4619_2208_2209 basis

theorem frame_4620_0_115 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 115 basis 4620=prefixState SixCarryPrefixData.program 0 basis 4620 := by
 exact at_between SixCarryPrefixData.program 0 115 4620 (by decide +kernel) nw_4620_0_115 basis

theorem frame_4620_116_813 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 813 basis 4620=prefixState SixCarryPrefixData.program 116 basis 4620 := by
 exact at_between SixCarryPrefixData.program 116 813 4620 (by decide +kernel) nw_4620_116_813 basis

theorem frame_4620_814_815 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 815 basis 4620=prefixState SixCarryPrefixData.program 814 basis 4620 := by
 exact at_between SixCarryPrefixData.program 814 815 4620 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 814 818 815 4620 (by decide +kernel) nw_4620_814_818) basis

theorem frame_4620_814_818 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 818 basis 4620=prefixState SixCarryPrefixData.program 814 basis 4620 := by
 exact at_between SixCarryPrefixData.program 814 818 4620 (by decide +kernel) nw_4620_814_818 basis

theorem frame_4620_819_984 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 984 basis 4620=prefixState SixCarryPrefixData.program 819 basis 4620 := by
 exact at_between SixCarryPrefixData.program 819 984 4620 (by decide +kernel) nw_4620_819_984 basis

theorem frame_4620_985_985 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 985 basis 4620=prefixState SixCarryPrefixData.program 985 basis 4620 := by
 rfl

theorem frame_4620_986_1426 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1426 basis 4620=prefixState SixCarryPrefixData.program 986 basis 4620 := by
 exact at_between SixCarryPrefixData.program 986 1426 4620 (by decide +kernel) nw_4620_986_1426 basis

theorem frame_4620_1427_2213 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2213 basis 4620=prefixState SixCarryPrefixData.program 1427 basis 4620 := by
 exact at_between SixCarryPrefixData.program 1427 2213 4620 (by decide +kernel) nw_4620_1427_2213 basis

theorem frame_4620_2214_2215 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2215 basis 4620=prefixState SixCarryPrefixData.program 2214 basis 4620 := by
 exact at_between SixCarryPrefixData.program 2214 2215 4620 (by decide +kernel) nw_4620_2214_2215 basis

theorem frame_4621_0_116 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 116 basis 4621=prefixState SixCarryPrefixData.program 0 basis 4621 := by
 exact at_between SixCarryPrefixData.program 0 116 4621 (by decide +kernel) nw_4621_0_116 basis

theorem frame_4621_117_819 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 819 basis 4621=prefixState SixCarryPrefixData.program 117 basis 4621 := by
 exact at_between SixCarryPrefixData.program 117 819 4621 (by decide +kernel) nw_4621_117_819 basis

theorem frame_4621_820_821 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 821 basis 4621=prefixState SixCarryPrefixData.program 820 basis 4621 := by
 exact at_between SixCarryPrefixData.program 820 821 4621 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 820 824 821 4621 (by decide +kernel) nw_4621_820_824) basis

theorem frame_4621_820_824 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 824 basis 4621=prefixState SixCarryPrefixData.program 820 basis 4621 := by
 exact at_between SixCarryPrefixData.program 820 824 4621 (by decide +kernel) nw_4621_820_824 basis

theorem frame_4621_825_981 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 981 basis 4621=prefixState SixCarryPrefixData.program 825 basis 4621 := by
 exact at_between SixCarryPrefixData.program 825 981 4621 (by decide +kernel) nw_4621_825_981 basis

theorem frame_4621_982_982 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 982 basis 4621=prefixState SixCarryPrefixData.program 982 basis 4621 := by
 rfl

theorem frame_4621_983_1427 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1427 basis 4621=prefixState SixCarryPrefixData.program 983 basis 4621 := by
 exact at_between SixCarryPrefixData.program 983 1427 4621 (by decide +kernel) nw_4621_983_1427 basis

theorem frame_4621_1428_2219 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2219 basis 4621=prefixState SixCarryPrefixData.program 1428 basis 4621 := by
 exact at_between SixCarryPrefixData.program 1428 2219 4621 (by decide +kernel) nw_4621_1428_2219 basis

theorem frame_4621_2220_2221 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2221 basis 4621=prefixState SixCarryPrefixData.program 2220 basis 4621 := by
 exact at_between SixCarryPrefixData.program 2220 2221 4621 (by decide +kernel) nw_4621_2220_2221 basis

theorem frame_4622_0_117 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 117 basis 4622=prefixState SixCarryPrefixData.program 0 basis 4622 := by
 exact at_between SixCarryPrefixData.program 0 117 4622 (by decide +kernel) nw_4622_0_117 basis

theorem frame_4622_118_825 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 825 basis 4622=prefixState SixCarryPrefixData.program 118 basis 4622 := by
 exact at_between SixCarryPrefixData.program 118 825 4622 (by decide +kernel) nw_4622_118_825 basis

theorem frame_4622_826_827 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 827 basis 4622=prefixState SixCarryPrefixData.program 826 basis 4622 := by
 exact at_between SixCarryPrefixData.program 826 827 4622 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 826 830 827 4622 (by decide +kernel) nw_4622_826_830) basis

theorem frame_4622_826_830 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 830 basis 4622=prefixState SixCarryPrefixData.program 826 basis 4622 := by
 exact at_between SixCarryPrefixData.program 826 830 4622 (by decide +kernel) nw_4622_826_830 basis

theorem frame_4622_831_978 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 978 basis 4622=prefixState SixCarryPrefixData.program 831 basis 4622 := by
 exact at_between SixCarryPrefixData.program 831 978 4622 (by decide +kernel) nw_4622_831_978 basis

theorem frame_4622_979_979 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 979 basis 4622=prefixState SixCarryPrefixData.program 979 basis 4622 := by
 rfl

theorem frame_4622_980_1428 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1428 basis 4622=prefixState SixCarryPrefixData.program 980 basis 4622 := by
 exact at_between SixCarryPrefixData.program 980 1428 4622 (by decide +kernel) nw_4622_980_1428 basis

theorem frame_4622_1429_2225 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2225 basis 4622=prefixState SixCarryPrefixData.program 1429 basis 4622 := by
 exact at_between SixCarryPrefixData.program 1429 2225 4622 (by decide +kernel) nw_4622_1429_2225 basis

theorem frame_4622_2226_2227 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2227 basis 4622=prefixState SixCarryPrefixData.program 2226 basis 4622 := by
 exact at_between SixCarryPrefixData.program 2226 2227 4622 (by decide +kernel) nw_4622_2226_2227 basis

theorem frame_4623_0_118 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 118 basis 4623=prefixState SixCarryPrefixData.program 0 basis 4623 := by
 exact at_between SixCarryPrefixData.program 0 118 4623 (by decide +kernel) nw_4623_0_118 basis

theorem frame_4623_119_831 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 831 basis 4623=prefixState SixCarryPrefixData.program 119 basis 4623 := by
 exact at_between SixCarryPrefixData.program 119 831 4623 (by decide +kernel) nw_4623_119_831 basis

theorem frame_4623_832_833 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 833 basis 4623=prefixState SixCarryPrefixData.program 832 basis 4623 := by
 exact at_between SixCarryPrefixData.program 832 833 4623 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 832 836 833 4623 (by decide +kernel) nw_4623_832_836) basis

theorem frame_4623_832_836 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 836 basis 4623=prefixState SixCarryPrefixData.program 832 basis 4623 := by
 exact at_between SixCarryPrefixData.program 832 836 4623 (by decide +kernel) nw_4623_832_836 basis

theorem frame_4623_837_975 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 975 basis 4623=prefixState SixCarryPrefixData.program 837 basis 4623 := by
 exact at_between SixCarryPrefixData.program 837 975 4623 (by decide +kernel) nw_4623_837_975 basis

theorem frame_4623_976_976 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 976 basis 4623=prefixState SixCarryPrefixData.program 976 basis 4623 := by
 rfl

theorem frame_4623_977_1429 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1429 basis 4623=prefixState SixCarryPrefixData.program 977 basis 4623 := by
 exact at_between SixCarryPrefixData.program 977 1429 4623 (by decide +kernel) nw_4623_977_1429 basis

theorem frame_4623_1430_2231 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2231 basis 4623=prefixState SixCarryPrefixData.program 1430 basis 4623 := by
 exact at_between SixCarryPrefixData.program 1430 2231 4623 (by decide +kernel) nw_4623_1430_2231 basis

theorem frame_4623_2232_2233 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2233 basis 4623=prefixState SixCarryPrefixData.program 2232 basis 4623 := by
 exact at_between SixCarryPrefixData.program 2232 2233 4623 (by decide +kernel) nw_4623_2232_2233 basis

theorem frame_4624_0_119 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 119 basis 4624=prefixState SixCarryPrefixData.program 0 basis 4624 := by
 exact at_between SixCarryPrefixData.program 0 119 4624 (by decide +kernel) nw_4624_0_119 basis

theorem frame_4624_120_837 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 837 basis 4624=prefixState SixCarryPrefixData.program 120 basis 4624 := by
 exact at_between SixCarryPrefixData.program 120 837 4624 (by decide +kernel) nw_4624_120_837 basis

theorem frame_4624_838_839 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 839 basis 4624=prefixState SixCarryPrefixData.program 838 basis 4624 := by
 exact at_between SixCarryPrefixData.program 838 839 4624 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 838 842 839 4624 (by decide +kernel) nw_4624_838_842) basis

theorem frame_4624_838_842 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 842 basis 4624=prefixState SixCarryPrefixData.program 838 basis 4624 := by
 exact at_between SixCarryPrefixData.program 838 842 4624 (by decide +kernel) nw_4624_838_842 basis

theorem frame_4624_843_972 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 972 basis 4624=prefixState SixCarryPrefixData.program 843 basis 4624 := by
 exact at_between SixCarryPrefixData.program 843 972 4624 (by decide +kernel) nw_4624_843_972 basis

theorem frame_4624_973_973 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 973 basis 4624=prefixState SixCarryPrefixData.program 973 basis 4624 := by
 rfl

theorem frame_4624_974_1430 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1430 basis 4624=prefixState SixCarryPrefixData.program 974 basis 4624 := by
 exact at_between SixCarryPrefixData.program 974 1430 4624 (by decide +kernel) nw_4624_974_1430 basis

theorem frame_4624_1431_2237 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2237 basis 4624=prefixState SixCarryPrefixData.program 1431 basis 4624 := by
 exact at_between SixCarryPrefixData.program 1431 2237 4624 (by decide +kernel) nw_4624_1431_2237 basis

theorem frame_4624_2238_2239 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2239 basis 4624=prefixState SixCarryPrefixData.program 2238 basis 4624 := by
 exact at_between SixCarryPrefixData.program 2238 2239 4624 (by decide +kernel) nw_4624_2238_2239 basis

theorem frame_4625_0_120 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 120 basis 4625=prefixState SixCarryPrefixData.program 0 basis 4625 := by
 exact at_between SixCarryPrefixData.program 0 120 4625 (by decide +kernel) nw_4625_0_120 basis

theorem frame_4625_121_843 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 843 basis 4625=prefixState SixCarryPrefixData.program 121 basis 4625 := by
 exact at_between SixCarryPrefixData.program 121 843 4625 (by decide +kernel) nw_4625_121_843 basis

theorem frame_4625_844_845 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 845 basis 4625=prefixState SixCarryPrefixData.program 844 basis 4625 := by
 exact at_between SixCarryPrefixData.program 844 845 4625 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 844 848 845 4625 (by decide +kernel) nw_4625_844_848) basis

theorem frame_4625_844_848 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 848 basis 4625=prefixState SixCarryPrefixData.program 844 basis 4625 := by
 exact at_between SixCarryPrefixData.program 844 848 4625 (by decide +kernel) nw_4625_844_848 basis

theorem frame_4625_849_969 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 969 basis 4625=prefixState SixCarryPrefixData.program 849 basis 4625 := by
 exact at_between SixCarryPrefixData.program 849 969 4625 (by decide +kernel) nw_4625_849_969 basis

theorem frame_4625_970_970 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 970 basis 4625=prefixState SixCarryPrefixData.program 970 basis 4625 := by
 rfl

theorem frame_4625_971_1431 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1431 basis 4625=prefixState SixCarryPrefixData.program 971 basis 4625 := by
 exact at_between SixCarryPrefixData.program 971 1431 4625 (by decide +kernel) nw_4625_971_1431 basis

theorem frame_4625_1432_2243 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2243 basis 4625=prefixState SixCarryPrefixData.program 1432 basis 4625 := by
 exact at_between SixCarryPrefixData.program 1432 2243 4625 (by decide +kernel) nw_4625_1432_2243 basis

theorem frame_4625_2244_2245 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2245 basis 4625=prefixState SixCarryPrefixData.program 2244 basis 4625 := by
 exact at_between SixCarryPrefixData.program 2244 2245 4625 (by decide +kernel) nw_4625_2244_2245 basis

theorem frame_4626_0_121 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 121 basis 4626=prefixState SixCarryPrefixData.program 0 basis 4626 := by
 exact at_between SixCarryPrefixData.program 0 121 4626 (by decide +kernel) nw_4626_0_121 basis

theorem frame_4626_122_849 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 849 basis 4626=prefixState SixCarryPrefixData.program 122 basis 4626 := by
 exact at_between SixCarryPrefixData.program 122 849 4626 (by decide +kernel) nw_4626_122_849 basis

theorem frame_4626_850_851 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 851 basis 4626=prefixState SixCarryPrefixData.program 850 basis 4626 := by
 exact at_between SixCarryPrefixData.program 850 851 4626 (by decide +kernel) (noWrite_mono_end SixCarryPrefixData.program 850 854 851 4626 (by decide +kernel) nw_4626_850_854) basis

theorem frame_4626_850_854 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 854 basis 4626=prefixState SixCarryPrefixData.program 850 basis 4626 := by
 exact at_between SixCarryPrefixData.program 850 854 4626 (by decide +kernel) nw_4626_850_854 basis

theorem frame_4626_855_966 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 966 basis 4626=prefixState SixCarryPrefixData.program 855 basis 4626 := by
 exact at_between SixCarryPrefixData.program 855 966 4626 (by decide +kernel) nw_4626_855_966 basis

theorem frame_4626_967_967 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 967 basis 4626=prefixState SixCarryPrefixData.program 967 basis 4626 := by
 rfl

theorem frame_4626_968_1432 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1432 basis 4626=prefixState SixCarryPrefixData.program 968 basis 4626 := by
 exact at_between SixCarryPrefixData.program 968 1432 4626 (by decide +kernel) nw_4626_968_1432 basis

theorem frame_4626_1433_2249 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2249 basis 4626=prefixState SixCarryPrefixData.program 1433 basis 4626 := by
 exact at_between SixCarryPrefixData.program 1433 2249 4626 (by decide +kernel) nw_4626_1433_2249 basis

theorem frame_4626_2250_2251 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2251 basis 4626=prefixState SixCarryPrefixData.program 2250 basis 4626 := by
 exact at_between SixCarryPrefixData.program 2250 2251 4626 (by decide +kernel) nw_4626_2250_2251 basis

theorem gate_102 : SixCarryPrefixData.program[102]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4607 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 102 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[102]?=some (.CX 4345 4607) := by decide +kernel
 have hh : SixCarryPrefixData.program[102]?=some (.CX 4345 4607) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_102 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 103 basis 4607=((prefixState SixCarryPrefixData.program 0 basis 4607) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 102 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4607
 rw [gate_102] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_102 basis,frame_4607_0_102 basis] at h
 exact h

theorem gate_103 : SixCarryPrefixData.program[103]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4608 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 103 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[103]?=some (.CX 4346 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[103]?=some (.CX 4346 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_103 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 104 basis 4608=((prefixState SixCarryPrefixData.program 0 basis 4608) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 103 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_103] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_103 basis,frame_4608_0_103 basis] at h
 exact h

theorem gate_104 : SixCarryPrefixData.program[104]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4609 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 104 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[104]?=some (.CX 4347 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[104]?=some (.CX 4347 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_104 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 105 basis 4609=((prefixState SixCarryPrefixData.program 0 basis 4609) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 104 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_104] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_104 basis,frame_4609_0_104 basis] at h
 exact h

theorem gate_108 : SixCarryPrefixData.program[108]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4613 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 108 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[108]?=some (.CX 4351 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[108]?=some (.CX 4351 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_108 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 109 basis 4613=((prefixState SixCarryPrefixData.program 0 basis 4613) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 108 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_108] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_108 basis,frame_4613_0_108 basis] at h
 exact h

theorem gate_109 : SixCarryPrefixData.program[109]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4614 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 109 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[109]?=some (.CX 4352 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[109]?=some (.CX 4352 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_109 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 110 basis 4614=((prefixState SixCarryPrefixData.program 0 basis 4614) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 109 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_109] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_109 basis,frame_4614_0_109 basis] at h
 exact h

theorem gate_110 : SixCarryPrefixData.program[110]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4615 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 110 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[110]?=some (.CX 4353 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[110]?=some (.CX 4353 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_110 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 111 basis 4615=((prefixState SixCarryPrefixData.program 0 basis 4615) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 110 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_110] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_110 basis,frame_4615_0_110 basis] at h
 exact h

theorem gate_111 : SixCarryPrefixData.program[111]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4616 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 111 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[111]?=some (.CX 4354 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[111]?=some (.CX 4354 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_111 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 112 basis 4616=((prefixState SixCarryPrefixData.program 0 basis 4616) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 111 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_111] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_111 basis,frame_4616_0_111 basis] at h
 exact h

theorem gate_112 : SixCarryPrefixData.program[112]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4617 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 112 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[112]?=some (.CX 4355 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[112]?=some (.CX 4355 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_112 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 113 basis 4617=((prefixState SixCarryPrefixData.program 0 basis 4617) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 112 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_112] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_112 basis,frame_4617_0_112 basis] at h
 exact h

theorem gate_113 : SixCarryPrefixData.program[113]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4618 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 113 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[113]?=some (.CX 4356 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[113]?=some (.CX 4356 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_113 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 114 basis 4618=((prefixState SixCarryPrefixData.program 0 basis 4618) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 113 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_113] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_113 basis,frame_4618_0_113 basis] at h
 exact h

theorem gate_114 : SixCarryPrefixData.program[114]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4619 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 114 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[114]?=some (.CX 4357 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[114]?=some (.CX 4357 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_114 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 115 basis 4619=((prefixState SixCarryPrefixData.program 0 basis 4619) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 114 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_114] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_114 basis,frame_4619_0_114 basis] at h
 exact h

theorem gate_115 : SixCarryPrefixData.program[115]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4620 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 115 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[115]?=some (.CX 4358 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[115]?=some (.CX 4358 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_115 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 116 basis 4620=((prefixState SixCarryPrefixData.program 0 basis 4620) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 115 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_115] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_115 basis,frame_4620_0_115 basis] at h
 exact h

theorem gate_116 : SixCarryPrefixData.program[116]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4359 4621 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 116 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[116]?=some (.CX 4359 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[116]?=some (.CX 4359 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_116 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 117 basis 4621=((prefixState SixCarryPrefixData.program 0 basis 4621) ^^ (prefixState SixCarryPrefixData.program 0 basis 4359)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 116 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_116] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4359_0_116 basis,frame_4621_0_116 basis] at h
 exact h

theorem gate_117 : SixCarryPrefixData.program[117]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4360 4622 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 117 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[117]?=some (.CX 4360 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[117]?=some (.CX 4360 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_117 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 118 basis 4622=((prefixState SixCarryPrefixData.program 0 basis 4622) ^^ (prefixState SixCarryPrefixData.program 0 basis 4360)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 117 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_117] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4360_0_117 basis,frame_4622_0_117 basis] at h
 exact h

theorem gate_118 : SixCarryPrefixData.program[118]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4361 4623 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 118 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[118]?=some (.CX 4361 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[118]?=some (.CX 4361 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_118 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 119 basis 4623=((prefixState SixCarryPrefixData.program 0 basis 4623) ^^ (prefixState SixCarryPrefixData.program 0 basis 4361)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 118 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_118] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4361_0_118 basis,frame_4623_0_118 basis] at h
 exact h

theorem gate_119 : SixCarryPrefixData.program[119]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4362 4624 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 119 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[119]?=some (.CX 4362 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[119]?=some (.CX 4362 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_119 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 120 basis 4624=((prefixState SixCarryPrefixData.program 0 basis 4624) ^^ (prefixState SixCarryPrefixData.program 0 basis 4362)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 119 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_119] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4362_0_119 basis,frame_4624_0_119 basis] at h
 exact h

theorem gate_120 : SixCarryPrefixData.program[120]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4363 4625 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 120 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[120]?=some (.CX 4363 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[120]?=some (.CX 4363 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_120 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 121 basis 4625=((prefixState SixCarryPrefixData.program 0 basis 4625) ^^ (prefixState SixCarryPrefixData.program 0 basis 4363)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 120 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_120] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4363_0_120 basis,frame_4625_0_120 basis] at h
 exact h

theorem gate_121 : SixCarryPrefixData.program[121]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4364 4626 := by
 have h := lookup_context SixCarryPrefixData.program before0 SixCarryPrefixData.chunk0 after0 0 121 shape0 before_len0 (by rw [len0]; decide +kernel)
 have hg : SixCarryPrefixData.chunk0[121]?=some (.CX 4364 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[121]?=some (.CX 4364 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_121 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 122 basis 4626=((prefixState SixCarryPrefixData.program 0 basis 4626) ^^ (prefixState SixCarryPrefixData.program 0 basis 4364)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 121 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_121] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4364_0_121 basis,frame_4626_0_121 basis] at h
 exact h

theorem gate_735 : SixCarryPrefixData.program[735]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4339 4607 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 95 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[95]?=some (.CX 4339 4607) := by decide +kernel
 have hh : SixCarryPrefixData.program[735]?=some (.CX 4339 4607) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_735 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 736 basis 4607=((prefixState SixCarryPrefixData.program 103 basis 4607) ^^ (prefixState SixCarryPrefixData.program 0 basis 4339)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 735 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4607
 rw [gate_735] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4339_0_735 basis,frame_4607_103_735 basis] at h
 exact h

theorem gate_737 : SixCarryPrefixData.program[737]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4607 4468 4469 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 97 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[97]?=some (.CCX 4607 4468 4469) := by decide +kernel
 have hh : SixCarryPrefixData.program[737]?=some (.CCX 4607 4468 4469) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_737 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 738 basis 4469=((prefixState SixCarryPrefixData.program 0 basis 4469) ^^ ((prefixState SixCarryPrefixData.program 736 basis 4607) && (prefixState SixCarryPrefixData.program 737 basis 4468))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 737 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4469
 rw [gate_737] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4469_0_737 basis,frame_4607_736_737 basis] at h
 exact h

theorem gate_738 : SixCarryPrefixData.program[738]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4339 4469 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 98 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[98]?=some (.CX 4339 4469) := by decide +kernel
 have hh : SixCarryPrefixData.program[738]?=some (.CX 4339 4469) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_738 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 739 basis 4469=((prefixState SixCarryPrefixData.program 738 basis 4469) ^^ (prefixState SixCarryPrefixData.program 0 basis 4339)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 738 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4469
 rw [gate_738] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4339_0_738 basis] at h
 exact h

theorem gate_741 : SixCarryPrefixData.program[741]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4608 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 101 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[101]?=some (.CX 4340 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[741]?=some (.CX 4340 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_741 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 742 basis 4608=((prefixState SixCarryPrefixData.program 104 basis 4608) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 741 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_741] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_741 basis,frame_4608_104_741 basis] at h
 exact h

theorem gate_742 : SixCarryPrefixData.program[742]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4469 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 102 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[102]?=some (.CX 4340 4469) := by decide +kernel
 have hh : SixCarryPrefixData.program[742]?=some (.CX 4340 4469) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_742 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 743 basis 4469=((prefixState SixCarryPrefixData.program 739 basis 4469) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 742 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4469
 rw [gate_742] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_742 basis,frame_4469_739_742 basis] at h
 exact h

theorem gate_743 : SixCarryPrefixData.program[743]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4608 4469 4470 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 103 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[103]?=some (.CCX 4608 4469 4470) := by decide +kernel
 have hh : SixCarryPrefixData.program[743]?=some (.CCX 4608 4469 4470) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_743 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 744 basis 4470=((prefixState SixCarryPrefixData.program 0 basis 4470) ^^ ((prefixState SixCarryPrefixData.program 742 basis 4608) && (prefixState SixCarryPrefixData.program 743 basis 4469))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 743 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4470
 rw [gate_743] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4470_0_743 basis,frame_4608_742_743 basis] at h
 exact h

theorem gate_744 : SixCarryPrefixData.program[744]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4470 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 104 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[104]?=some (.CX 4340 4470) := by decide +kernel
 have hh : SixCarryPrefixData.program[744]?=some (.CX 4340 4470) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_744 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 745 basis 4470=((prefixState SixCarryPrefixData.program 744 basis 4470) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 744 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4470
 rw [gate_744] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_744 basis] at h
 exact h

theorem gate_745 : SixCarryPrefixData.program[745]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4469 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 105 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[105]?=some (.CX 4340 4469) := by decide +kernel
 have hh : SixCarryPrefixData.program[745]?=some (.CX 4340 4469) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_745 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 746 basis 4469=((prefixState SixCarryPrefixData.program 743 basis 4469) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 745 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4469
 rw [gate_745] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_745 basis,frame_4469_743_745 basis] at h
 exact h

theorem gate_746 : SixCarryPrefixData.program[746]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4608 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 106 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[106]?=some (.CX 4340 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[746]?=some (.CX 4340 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_746 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 747 basis 4608=((prefixState SixCarryPrefixData.program 742 basis 4608) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 746 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_746] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_746 basis,frame_4608_742_746 basis] at h
 exact h

theorem gate_747 : SixCarryPrefixData.program[747]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4341 4609 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 107 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[107]?=some (.CX 4341 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[747]?=some (.CX 4341 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_747 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 748 basis 4609=((prefixState SixCarryPrefixData.program 105 basis 4609) ^^ (prefixState SixCarryPrefixData.program 0 basis 4341)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 747 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_747] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4341_0_747 basis,frame_4609_105_747 basis] at h
 exact h

theorem gate_748 : SixCarryPrefixData.program[748]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4341 4470 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 108 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[108]?=some (.CX 4341 4470) := by decide +kernel
 have hh : SixCarryPrefixData.program[748]?=some (.CX 4341 4470) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_748 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 749 basis 4470=((prefixState SixCarryPrefixData.program 745 basis 4470) ^^ (prefixState SixCarryPrefixData.program 0 basis 4341)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 748 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4470
 rw [gate_748] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4341_0_748 basis,frame_4470_745_748 basis] at h
 exact h

theorem gate_751 : SixCarryPrefixData.program[751]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4341 4470 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 111 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[111]?=some (.CX 4341 4470) := by decide +kernel
 have hh : SixCarryPrefixData.program[751]?=some (.CX 4341 4470) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_751 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 752 basis 4470=((prefixState SixCarryPrefixData.program 749 basis 4470) ^^ (prefixState SixCarryPrefixData.program 0 basis 4341)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 751 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4470
 rw [gate_751] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4341_0_751 basis,frame_4470_749_751 basis] at h
 exact h

theorem gate_752 : SixCarryPrefixData.program[752]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4341 4609 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 112 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[112]?=some (.CX 4341 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[752]?=some (.CX 4341 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_752 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 753 basis 4609=((prefixState SixCarryPrefixData.program 748 basis 4609) ^^ (prefixState SixCarryPrefixData.program 0 basis 4341)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 752 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_752] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4341_0_752 basis,frame_4609_748_752 basis] at h
 exact h

theorem gate_767 : SixCarryPrefixData.program[767]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4612 4473 4474 := by
 have h := lookup_context SixCarryPrefixData.program before5 SixCarryPrefixData.chunk5 after5 640 127 shape5 before_len5 (by rw [len5]; decide +kernel)
 have hg : SixCarryPrefixData.chunk5[127]?=some (.CCX 4612 4473 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[767]?=some (.CCX 4612 4473 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_767 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 768 basis 4474=((prefixState SixCarryPrefixData.program 0 basis 4474) ^^ ((prefixState SixCarryPrefixData.program 766 basis 4612) && (prefixState SixCarryPrefixData.program 767 basis 4473))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 767 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_767] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4474_0_767 basis,frame_4612_766_767 basis] at h
 exact h

theorem gate_768 : SixCarryPrefixData.program[768]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4474 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 0 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[0]?=some (.CX 4344 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[768]?=some (.CX 4344 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_768 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 769 basis 4474=((prefixState SixCarryPrefixData.program 768 basis 4474) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 768 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_768] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_768 basis] at h
 exact h

theorem gate_769 : SixCarryPrefixData.program[769]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4473 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 1 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[1]?=some (.CX 4344 4473) := by decide +kernel
 have hh : SixCarryPrefixData.program[769]?=some (.CX 4344 4473) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_769 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 770 basis 4473=((prefixState SixCarryPrefixData.program 767 basis 4473) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 769 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4473
 rw [gate_769] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_769 basis,frame_4473_767_769 basis] at h
 exact h

theorem gate_770 : SixCarryPrefixData.program[770]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4612 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 2 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[2]?=some (.CX 4344 4612) := by decide +kernel
 have hh : SixCarryPrefixData.program[770]?=some (.CX 4344 4612) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_770 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 771 basis 4612=((prefixState SixCarryPrefixData.program 766 basis 4612) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 770 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4612
 rw [gate_770] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_770 basis,frame_4612_766_770 basis] at h
 exact h

theorem gate_771 : SixCarryPrefixData.program[771]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4613 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 3 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[3]?=some (.CX 4345 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[771]?=some (.CX 4345 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_771 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 772 basis 4613=((prefixState SixCarryPrefixData.program 109 basis 4613) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 771 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_771] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_771 basis,frame_4613_109_771 basis] at h
 exact h

theorem gate_772 : SixCarryPrefixData.program[772]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4474 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 4 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[4]?=some (.CX 4345 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[772]?=some (.CX 4345 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_772 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 773 basis 4474=((prefixState SixCarryPrefixData.program 769 basis 4474) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 772 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_772] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_772 basis,frame_4474_769_772 basis] at h
 exact h

theorem gate_773 : SixCarryPrefixData.program[773]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4613 4474 4475 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 5 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[5]?=some (.CCX 4613 4474 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[773]?=some (.CCX 4613 4474 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_773 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 774 basis 4475=((prefixState SixCarryPrefixData.program 0 basis 4475) ^^ ((prefixState SixCarryPrefixData.program 772 basis 4613) && (prefixState SixCarryPrefixData.program 773 basis 4474))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 773 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_773] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4475_0_773 basis,frame_4613_772_773 basis] at h
 exact h

theorem gate_774 : SixCarryPrefixData.program[774]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4475 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 6 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[6]?=some (.CX 4345 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[774]?=some (.CX 4345 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_774 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 775 basis 4475=((prefixState SixCarryPrefixData.program 774 basis 4475) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 774 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_774] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_774 basis] at h
 exact h

theorem gate_775 : SixCarryPrefixData.program[775]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4474 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 7 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[7]?=some (.CX 4345 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[775]?=some (.CX 4345 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_775 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 776 basis 4474=((prefixState SixCarryPrefixData.program 773 basis 4474) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 775 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_775] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_775 basis,frame_4474_773_775 basis] at h
 exact h

theorem gate_776 : SixCarryPrefixData.program[776]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4613 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 8 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[8]?=some (.CX 4345 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[776]?=some (.CX 4345 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_776 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 777 basis 4613=((prefixState SixCarryPrefixData.program 772 basis 4613) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 776 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_776] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_776 basis,frame_4613_772_776 basis] at h
 exact h

theorem gate_777 : SixCarryPrefixData.program[777]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4614 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 9 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[9]?=some (.CX 4346 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[777]?=some (.CX 4346 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_777 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 778 basis 4614=((prefixState SixCarryPrefixData.program 110 basis 4614) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 777 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_777] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_777 basis,frame_4614_110_777 basis] at h
 exact h

theorem gate_778 : SixCarryPrefixData.program[778]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4475 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 10 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[10]?=some (.CX 4346 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[778]?=some (.CX 4346 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_778 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 779 basis 4475=((prefixState SixCarryPrefixData.program 775 basis 4475) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 778 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_778] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_778 basis,frame_4475_775_778 basis] at h
 exact h

theorem gate_779 : SixCarryPrefixData.program[779]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4614 4475 4476 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 11 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[11]?=some (.CCX 4614 4475 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[779]?=some (.CCX 4614 4475 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_779 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 780 basis 4476=((prefixState SixCarryPrefixData.program 0 basis 4476) ^^ ((prefixState SixCarryPrefixData.program 778 basis 4614) && (prefixState SixCarryPrefixData.program 779 basis 4475))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 779 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_779] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4476_0_779 basis,frame_4614_778_779 basis] at h
 exact h

theorem gate_780 : SixCarryPrefixData.program[780]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4476 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 12 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[12]?=some (.CX 4346 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[780]?=some (.CX 4346 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_780 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 781 basis 4476=((prefixState SixCarryPrefixData.program 780 basis 4476) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 780 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_780] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_780 basis] at h
 exact h

theorem gate_781 : SixCarryPrefixData.program[781]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4475 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 13 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[13]?=some (.CX 4346 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[781]?=some (.CX 4346 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_781 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 782 basis 4475=((prefixState SixCarryPrefixData.program 779 basis 4475) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 781 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_781] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_781 basis,frame_4475_779_781 basis] at h
 exact h

theorem gate_782 : SixCarryPrefixData.program[782]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4614 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 14 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[14]?=some (.CX 4346 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[782]?=some (.CX 4346 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_782 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 783 basis 4614=((prefixState SixCarryPrefixData.program 778 basis 4614) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 782 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_782] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_782 basis,frame_4614_778_782 basis] at h
 exact h

theorem gate_783 : SixCarryPrefixData.program[783]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4615 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 15 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[15]?=some (.CX 4347 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[783]?=some (.CX 4347 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_783 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 784 basis 4615=((prefixState SixCarryPrefixData.program 111 basis 4615) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 783 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_783] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_783 basis,frame_4615_111_783 basis] at h
 exact h

theorem gate_784 : SixCarryPrefixData.program[784]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4476 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 16 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[16]?=some (.CX 4347 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[784]?=some (.CX 4347 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_784 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 785 basis 4476=((prefixState SixCarryPrefixData.program 781 basis 4476) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 784 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_784] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_784 basis,frame_4476_781_784 basis] at h
 exact h

theorem gate_785 : SixCarryPrefixData.program[785]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4615 4476 4477 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 17 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[17]?=some (.CCX 4615 4476 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[785]?=some (.CCX 4615 4476 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_785 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 786 basis 4477=((prefixState SixCarryPrefixData.program 0 basis 4477) ^^ ((prefixState SixCarryPrefixData.program 784 basis 4615) && (prefixState SixCarryPrefixData.program 785 basis 4476))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 785 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_785] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4477_0_785 basis,frame_4615_784_785 basis] at h
 exact h

theorem gate_786 : SixCarryPrefixData.program[786]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4477 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 18 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[18]?=some (.CX 4347 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[786]?=some (.CX 4347 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_786 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 787 basis 4477=((prefixState SixCarryPrefixData.program 786 basis 4477) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 786 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_786] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_786 basis] at h
 exact h

theorem gate_787 : SixCarryPrefixData.program[787]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4476 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 19 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[19]?=some (.CX 4347 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[787]?=some (.CX 4347 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_787 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 788 basis 4476=((prefixState SixCarryPrefixData.program 785 basis 4476) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 787 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_787] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_787 basis,frame_4476_785_787 basis] at h
 exact h

theorem gate_788 : SixCarryPrefixData.program[788]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4615 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 20 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[20]?=some (.CX 4347 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[788]?=some (.CX 4347 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_788 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 789 basis 4615=((prefixState SixCarryPrefixData.program 784 basis 4615) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 788 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_788] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_788 basis,frame_4615_784_788 basis] at h
 exact h

theorem gate_789 : SixCarryPrefixData.program[789]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4616 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 21 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[21]?=some (.CX 4348 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[789]?=some (.CX 4348 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_789 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 790 basis 4616=((prefixState SixCarryPrefixData.program 112 basis 4616) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 789 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_789] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_789 basis,frame_4616_112_789 basis] at h
 exact h

theorem gate_790 : SixCarryPrefixData.program[790]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4477 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 22 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[22]?=some (.CX 4348 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[790]?=some (.CX 4348 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_790 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 791 basis 4477=((prefixState SixCarryPrefixData.program 787 basis 4477) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 790 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_790] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_790 basis,frame_4477_787_790 basis] at h
 exact h

theorem gate_791 : SixCarryPrefixData.program[791]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4616 4477 4478 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 23 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[23]?=some (.CCX 4616 4477 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[791]?=some (.CCX 4616 4477 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_791 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 792 basis 4478=((prefixState SixCarryPrefixData.program 0 basis 4478) ^^ ((prefixState SixCarryPrefixData.program 790 basis 4616) && (prefixState SixCarryPrefixData.program 791 basis 4477))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 791 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_791] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4478_0_791 basis,frame_4616_790_791 basis] at h
 exact h

theorem gate_792 : SixCarryPrefixData.program[792]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4478 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 24 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[24]?=some (.CX 4348 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[792]?=some (.CX 4348 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_792 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 793 basis 4478=((prefixState SixCarryPrefixData.program 792 basis 4478) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 792 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_792] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_792 basis] at h
 exact h

theorem gate_793 : SixCarryPrefixData.program[793]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4477 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 25 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[25]?=some (.CX 4348 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[793]?=some (.CX 4348 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_793 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 794 basis 4477=((prefixState SixCarryPrefixData.program 791 basis 4477) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 793 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_793] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_793 basis,frame_4477_791_793 basis] at h
 exact h

theorem gate_794 : SixCarryPrefixData.program[794]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4616 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 26 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[26]?=some (.CX 4348 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[794]?=some (.CX 4348 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_794 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 795 basis 4616=((prefixState SixCarryPrefixData.program 790 basis 4616) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 794 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_794] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_794 basis,frame_4616_790_794 basis] at h
 exact h

theorem gate_795 : SixCarryPrefixData.program[795]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4617 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 27 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[27]?=some (.CX 4349 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[795]?=some (.CX 4349 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_795 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 796 basis 4617=((prefixState SixCarryPrefixData.program 113 basis 4617) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 795 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_795] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_795 basis,frame_4617_113_795 basis] at h
 exact h

theorem gate_796 : SixCarryPrefixData.program[796]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4478 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 28 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[28]?=some (.CX 4349 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[796]?=some (.CX 4349 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_796 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 797 basis 4478=((prefixState SixCarryPrefixData.program 793 basis 4478) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 796 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_796] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_796 basis,frame_4478_793_796 basis] at h
 exact h

theorem gate_797 : SixCarryPrefixData.program[797]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4617 4478 4479 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 29 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[29]?=some (.CCX 4617 4478 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[797]?=some (.CCX 4617 4478 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_797 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 798 basis 4479=((prefixState SixCarryPrefixData.program 0 basis 4479) ^^ ((prefixState SixCarryPrefixData.program 796 basis 4617) && (prefixState SixCarryPrefixData.program 797 basis 4478))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 797 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_797] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4479_0_797 basis,frame_4617_796_797 basis] at h
 exact h

theorem gate_798 : SixCarryPrefixData.program[798]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4479 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 30 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[30]?=some (.CX 4349 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[798]?=some (.CX 4349 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_798 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 799 basis 4479=((prefixState SixCarryPrefixData.program 798 basis 4479) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 798 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_798] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_798 basis] at h
 exact h

theorem gate_799 : SixCarryPrefixData.program[799]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4478 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 31 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[31]?=some (.CX 4349 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[799]?=some (.CX 4349 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_799 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 800 basis 4478=((prefixState SixCarryPrefixData.program 797 basis 4478) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 799 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_799] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_799 basis,frame_4478_797_799 basis] at h
 exact h

theorem gate_800 : SixCarryPrefixData.program[800]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4617 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 32 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[32]?=some (.CX 4349 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[800]?=some (.CX 4349 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_800 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 801 basis 4617=((prefixState SixCarryPrefixData.program 796 basis 4617) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 800 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_800] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_800 basis,frame_4617_796_800 basis] at h
 exact h

theorem gate_801 : SixCarryPrefixData.program[801]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4618 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 33 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[33]?=some (.CX 4350 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[801]?=some (.CX 4350 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_801 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 802 basis 4618=((prefixState SixCarryPrefixData.program 114 basis 4618) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 801 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_801] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_801 basis,frame_4618_114_801 basis] at h
 exact h

theorem gate_802 : SixCarryPrefixData.program[802]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4479 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 34 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[34]?=some (.CX 4350 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[802]?=some (.CX 4350 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_802 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 803 basis 4479=((prefixState SixCarryPrefixData.program 799 basis 4479) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 802 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_802] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_802 basis,frame_4479_799_802 basis] at h
 exact h

theorem gate_803 : SixCarryPrefixData.program[803]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4618 4479 4480 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 35 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[35]?=some (.CCX 4618 4479 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[803]?=some (.CCX 4618 4479 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_803 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 804 basis 4480=((prefixState SixCarryPrefixData.program 0 basis 4480) ^^ ((prefixState SixCarryPrefixData.program 802 basis 4618) && (prefixState SixCarryPrefixData.program 803 basis 4479))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 803 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_803] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4480_0_803 basis,frame_4618_802_803 basis] at h
 exact h

theorem gate_804 : SixCarryPrefixData.program[804]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4480 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 36 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[36]?=some (.CX 4350 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[804]?=some (.CX 4350 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_804 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 805 basis 4480=((prefixState SixCarryPrefixData.program 804 basis 4480) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 804 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_804] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_804 basis] at h
 exact h

theorem gate_805 : SixCarryPrefixData.program[805]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4479 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 37 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[37]?=some (.CX 4350 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[805]?=some (.CX 4350 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_805 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 806 basis 4479=((prefixState SixCarryPrefixData.program 803 basis 4479) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 805 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_805] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_805 basis,frame_4479_803_805 basis] at h
 exact h

theorem gate_806 : SixCarryPrefixData.program[806]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4618 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 38 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[38]?=some (.CX 4350 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[806]?=some (.CX 4350 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_806 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 807 basis 4618=((prefixState SixCarryPrefixData.program 802 basis 4618) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 806 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_806] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_806 basis,frame_4618_802_806 basis] at h
 exact h

theorem gate_807 : SixCarryPrefixData.program[807]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4619 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 39 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[39]?=some (.CX 4351 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[807]?=some (.CX 4351 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_807 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 808 basis 4619=((prefixState SixCarryPrefixData.program 115 basis 4619) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 807 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_807] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_807 basis,frame_4619_115_807 basis] at h
 exact h

theorem gate_808 : SixCarryPrefixData.program[808]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4480 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 40 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[40]?=some (.CX 4351 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[808]?=some (.CX 4351 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_808 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 809 basis 4480=((prefixState SixCarryPrefixData.program 805 basis 4480) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 808 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_808] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_808 basis,frame_4480_805_808 basis] at h
 exact h

theorem gate_809 : SixCarryPrefixData.program[809]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4619 4480 4481 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 41 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[41]?=some (.CCX 4619 4480 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[809]?=some (.CCX 4619 4480 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_809 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 810 basis 4481=((prefixState SixCarryPrefixData.program 0 basis 4481) ^^ ((prefixState SixCarryPrefixData.program 808 basis 4619) && (prefixState SixCarryPrefixData.program 809 basis 4480))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 809 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_809] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4481_0_809 basis,frame_4619_808_809 basis] at h
 exact h

theorem gate_810 : SixCarryPrefixData.program[810]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4481 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 42 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[42]?=some (.CX 4351 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[810]?=some (.CX 4351 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_810 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 811 basis 4481=((prefixState SixCarryPrefixData.program 810 basis 4481) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 810 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_810] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_810 basis] at h
 exact h

theorem gate_811 : SixCarryPrefixData.program[811]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4480 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 43 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[43]?=some (.CX 4351 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[811]?=some (.CX 4351 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_811 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 812 basis 4480=((prefixState SixCarryPrefixData.program 809 basis 4480) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 811 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_811] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_811 basis,frame_4480_809_811 basis] at h
 exact h

theorem gate_812 : SixCarryPrefixData.program[812]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4619 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 44 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[44]?=some (.CX 4351 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[812]?=some (.CX 4351 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_812 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 813 basis 4619=((prefixState SixCarryPrefixData.program 808 basis 4619) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 812 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_812] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_812 basis,frame_4619_808_812 basis] at h
 exact h

theorem gate_813 : SixCarryPrefixData.program[813]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4620 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 45 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[45]?=some (.CX 4352 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[813]?=some (.CX 4352 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_813 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 814 basis 4620=((prefixState SixCarryPrefixData.program 116 basis 4620) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 813 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_813] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_813 basis,frame_4620_116_813 basis] at h
 exact h

theorem gate_814 : SixCarryPrefixData.program[814]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4481 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 46 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[46]?=some (.CX 4352 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[814]?=some (.CX 4352 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_814 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 815 basis 4481=((prefixState SixCarryPrefixData.program 811 basis 4481) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 814 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_814] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_814 basis,frame_4481_811_814 basis] at h
 exact h

theorem gate_815 : SixCarryPrefixData.program[815]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4620 4481 4482 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 47 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[47]?=some (.CCX 4620 4481 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[815]?=some (.CCX 4620 4481 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_815 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 816 basis 4482=((prefixState SixCarryPrefixData.program 0 basis 4482) ^^ ((prefixState SixCarryPrefixData.program 814 basis 4620) && (prefixState SixCarryPrefixData.program 815 basis 4481))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 815 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_815] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4482_0_815 basis,frame_4620_814_815 basis] at h
 exact h

theorem gate_816 : SixCarryPrefixData.program[816]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4482 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 48 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[48]?=some (.CX 4352 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[816]?=some (.CX 4352 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_816 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 817 basis 4482=((prefixState SixCarryPrefixData.program 816 basis 4482) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 816 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_816] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_816 basis] at h
 exact h

theorem gate_817 : SixCarryPrefixData.program[817]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4481 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 49 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[49]?=some (.CX 4352 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[817]?=some (.CX 4352 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_817 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 818 basis 4481=((prefixState SixCarryPrefixData.program 815 basis 4481) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 817 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_817] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_817 basis,frame_4481_815_817 basis] at h
 exact h

theorem gate_818 : SixCarryPrefixData.program[818]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4620 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 50 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[50]?=some (.CX 4352 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[818]?=some (.CX 4352 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_818 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 819 basis 4620=((prefixState SixCarryPrefixData.program 814 basis 4620) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 818 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_818] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_818 basis,frame_4620_814_818 basis] at h
 exact h

theorem gate_819 : SixCarryPrefixData.program[819]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4621 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 51 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[51]?=some (.CX 4353 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[819]?=some (.CX 4353 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_819 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 820 basis 4621=((prefixState SixCarryPrefixData.program 117 basis 4621) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 819 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_819] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_819 basis,frame_4621_117_819 basis] at h
 exact h

theorem gate_820 : SixCarryPrefixData.program[820]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4482 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 52 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[52]?=some (.CX 4353 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[820]?=some (.CX 4353 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_820 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 821 basis 4482=((prefixState SixCarryPrefixData.program 817 basis 4482) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 820 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_820] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_820 basis,frame_4482_817_820 basis] at h
 exact h

theorem gate_821 : SixCarryPrefixData.program[821]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4621 4482 4483 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 53 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[53]?=some (.CCX 4621 4482 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[821]?=some (.CCX 4621 4482 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_821 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 822 basis 4483=((prefixState SixCarryPrefixData.program 0 basis 4483) ^^ ((prefixState SixCarryPrefixData.program 820 basis 4621) && (prefixState SixCarryPrefixData.program 821 basis 4482))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 821 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_821] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4483_0_821 basis,frame_4621_820_821 basis] at h
 exact h

theorem gate_822 : SixCarryPrefixData.program[822]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4483 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 54 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[54]?=some (.CX 4353 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[822]?=some (.CX 4353 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_822 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 823 basis 4483=((prefixState SixCarryPrefixData.program 822 basis 4483) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 822 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_822] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_822 basis] at h
 exact h

theorem gate_823 : SixCarryPrefixData.program[823]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4482 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 55 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[55]?=some (.CX 4353 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[823]?=some (.CX 4353 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_823 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 824 basis 4482=((prefixState SixCarryPrefixData.program 821 basis 4482) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 823 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_823] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_823 basis,frame_4482_821_823 basis] at h
 exact h

theorem gate_824 : SixCarryPrefixData.program[824]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4621 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 56 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[56]?=some (.CX 4353 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[824]?=some (.CX 4353 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_824 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 825 basis 4621=((prefixState SixCarryPrefixData.program 820 basis 4621) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 824 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_824] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_824 basis,frame_4621_820_824 basis] at h
 exact h

theorem gate_825 : SixCarryPrefixData.program[825]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4622 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 57 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[57]?=some (.CX 4354 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[825]?=some (.CX 4354 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_825 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 826 basis 4622=((prefixState SixCarryPrefixData.program 118 basis 4622) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 825 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_825] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_825 basis,frame_4622_118_825 basis] at h
 exact h

theorem gate_826 : SixCarryPrefixData.program[826]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4483 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 58 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[58]?=some (.CX 4354 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[826]?=some (.CX 4354 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_826 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 827 basis 4483=((prefixState SixCarryPrefixData.program 823 basis 4483) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 826 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_826] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_826 basis,frame_4483_823_826 basis] at h
 exact h

theorem gate_827 : SixCarryPrefixData.program[827]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4622 4483 4484 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 59 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[59]?=some (.CCX 4622 4483 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[827]?=some (.CCX 4622 4483 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_827 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 828 basis 4484=((prefixState SixCarryPrefixData.program 0 basis 4484) ^^ ((prefixState SixCarryPrefixData.program 826 basis 4622) && (prefixState SixCarryPrefixData.program 827 basis 4483))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 827 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_827] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4484_0_827 basis,frame_4622_826_827 basis] at h
 exact h

theorem gate_828 : SixCarryPrefixData.program[828]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4484 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 60 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[60]?=some (.CX 4354 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[828]?=some (.CX 4354 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_828 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 829 basis 4484=((prefixState SixCarryPrefixData.program 828 basis 4484) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 828 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_828] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_828 basis] at h
 exact h

theorem gate_829 : SixCarryPrefixData.program[829]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4483 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 61 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[61]?=some (.CX 4354 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[829]?=some (.CX 4354 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_829 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 830 basis 4483=((prefixState SixCarryPrefixData.program 827 basis 4483) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 829 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_829] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_829 basis,frame_4483_827_829 basis] at h
 exact h

theorem gate_830 : SixCarryPrefixData.program[830]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4622 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 62 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[62]?=some (.CX 4354 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[830]?=some (.CX 4354 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_830 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 831 basis 4622=((prefixState SixCarryPrefixData.program 826 basis 4622) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 830 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_830] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_830 basis,frame_4622_826_830 basis] at h
 exact h

theorem gate_831 : SixCarryPrefixData.program[831]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4623 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 63 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[63]?=some (.CX 4355 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[831]?=some (.CX 4355 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_831 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 832 basis 4623=((prefixState SixCarryPrefixData.program 119 basis 4623) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 831 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_831] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_831 basis,frame_4623_119_831 basis] at h
 exact h

theorem gate_832 : SixCarryPrefixData.program[832]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4484 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 64 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[64]?=some (.CX 4355 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[832]?=some (.CX 4355 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_832 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 833 basis 4484=((prefixState SixCarryPrefixData.program 829 basis 4484) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 832 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_832] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_832 basis,frame_4484_829_832 basis] at h
 exact h

theorem gate_833 : SixCarryPrefixData.program[833]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4623 4484 4485 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 65 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[65]?=some (.CCX 4623 4484 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[833]?=some (.CCX 4623 4484 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_833 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 834 basis 4485=((prefixState SixCarryPrefixData.program 0 basis 4485) ^^ ((prefixState SixCarryPrefixData.program 832 basis 4623) && (prefixState SixCarryPrefixData.program 833 basis 4484))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 833 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_833] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4485_0_833 basis,frame_4623_832_833 basis] at h
 exact h

theorem gate_834 : SixCarryPrefixData.program[834]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4485 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 66 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[66]?=some (.CX 4355 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[834]?=some (.CX 4355 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_834 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 835 basis 4485=((prefixState SixCarryPrefixData.program 834 basis 4485) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 834 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_834] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_834 basis] at h
 exact h

theorem gate_835 : SixCarryPrefixData.program[835]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4484 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 67 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[67]?=some (.CX 4355 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[835]?=some (.CX 4355 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_835 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 836 basis 4484=((prefixState SixCarryPrefixData.program 833 basis 4484) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 835 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_835] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_835 basis,frame_4484_833_835 basis] at h
 exact h

theorem gate_836 : SixCarryPrefixData.program[836]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4623 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 68 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[68]?=some (.CX 4355 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[836]?=some (.CX 4355 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_836 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 837 basis 4623=((prefixState SixCarryPrefixData.program 832 basis 4623) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 836 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_836] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_836 basis,frame_4623_832_836 basis] at h
 exact h

theorem gate_837 : SixCarryPrefixData.program[837]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4624 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 69 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[69]?=some (.CX 4356 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[837]?=some (.CX 4356 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_837 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 838 basis 4624=((prefixState SixCarryPrefixData.program 120 basis 4624) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 837 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_837] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_837 basis,frame_4624_120_837 basis] at h
 exact h

theorem gate_838 : SixCarryPrefixData.program[838]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4485 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 70 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[70]?=some (.CX 4356 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[838]?=some (.CX 4356 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_838 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 839 basis 4485=((prefixState SixCarryPrefixData.program 835 basis 4485) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 838 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_838] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_838 basis,frame_4485_835_838 basis] at h
 exact h

theorem gate_839 : SixCarryPrefixData.program[839]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4624 4485 4486 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 71 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[71]?=some (.CCX 4624 4485 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[839]?=some (.CCX 4624 4485 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_839 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 840 basis 4486=((prefixState SixCarryPrefixData.program 0 basis 4486) ^^ ((prefixState SixCarryPrefixData.program 838 basis 4624) && (prefixState SixCarryPrefixData.program 839 basis 4485))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 839 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_839] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4486_0_839 basis,frame_4624_838_839 basis] at h
 exact h

theorem gate_840 : SixCarryPrefixData.program[840]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4486 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 72 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[72]?=some (.CX 4356 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[840]?=some (.CX 4356 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_840 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 841 basis 4486=((prefixState SixCarryPrefixData.program 840 basis 4486) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 840 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_840] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_840 basis] at h
 exact h

theorem gate_841 : SixCarryPrefixData.program[841]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4485 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 73 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[73]?=some (.CX 4356 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[841]?=some (.CX 4356 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_841 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 842 basis 4485=((prefixState SixCarryPrefixData.program 839 basis 4485) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 841 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_841] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_841 basis,frame_4485_839_841 basis] at h
 exact h

theorem gate_842 : SixCarryPrefixData.program[842]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4624 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 74 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[74]?=some (.CX 4356 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[842]?=some (.CX 4356 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_842 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 843 basis 4624=((prefixState SixCarryPrefixData.program 838 basis 4624) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 842 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_842] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_842 basis,frame_4624_838_842 basis] at h
 exact h

theorem gate_843 : SixCarryPrefixData.program[843]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4625 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 75 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[75]?=some (.CX 4357 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[843]?=some (.CX 4357 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_843 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 844 basis 4625=((prefixState SixCarryPrefixData.program 121 basis 4625) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 843 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_843] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_843 basis,frame_4625_121_843 basis] at h
 exact h

theorem gate_844 : SixCarryPrefixData.program[844]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4486 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 76 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[76]?=some (.CX 4357 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[844]?=some (.CX 4357 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_844 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 845 basis 4486=((prefixState SixCarryPrefixData.program 841 basis 4486) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 844 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_844] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_844 basis,frame_4486_841_844 basis] at h
 exact h

theorem gate_845 : SixCarryPrefixData.program[845]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4625 4486 4487 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 77 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[77]?=some (.CCX 4625 4486 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[845]?=some (.CCX 4625 4486 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_845 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 846 basis 4487=((prefixState SixCarryPrefixData.program 0 basis 4487) ^^ ((prefixState SixCarryPrefixData.program 844 basis 4625) && (prefixState SixCarryPrefixData.program 845 basis 4486))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 845 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_845] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4487_0_845 basis,frame_4625_844_845 basis] at h
 exact h

theorem gate_846 : SixCarryPrefixData.program[846]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4487 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 78 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[78]?=some (.CX 4357 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[846]?=some (.CX 4357 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_846 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 847 basis 4487=((prefixState SixCarryPrefixData.program 846 basis 4487) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 846 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_846] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_846 basis] at h
 exact h

theorem gate_847 : SixCarryPrefixData.program[847]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4486 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 79 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[79]?=some (.CX 4357 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[847]?=some (.CX 4357 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_847 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 848 basis 4486=((prefixState SixCarryPrefixData.program 845 basis 4486) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 847 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_847] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_847 basis,frame_4486_845_847 basis] at h
 exact h

theorem gate_848 : SixCarryPrefixData.program[848]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4625 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 80 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[80]?=some (.CX 4357 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[848]?=some (.CX 4357 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_848 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 849 basis 4625=((prefixState SixCarryPrefixData.program 844 basis 4625) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 848 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_848] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_848 basis,frame_4625_844_848 basis] at h
 exact h

theorem gate_849 : SixCarryPrefixData.program[849]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4626 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 81 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[81]?=some (.CX 4358 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[849]?=some (.CX 4358 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_849 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 850 basis 4626=((prefixState SixCarryPrefixData.program 122 basis 4626) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 849 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_849] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_849 basis,frame_4626_122_849 basis] at h
 exact h

theorem gate_850 : SixCarryPrefixData.program[850]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4487 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 82 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[82]?=some (.CX 4358 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[850]?=some (.CX 4358 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_850 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 851 basis 4487=((prefixState SixCarryPrefixData.program 847 basis 4487) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 850 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_850] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_850 basis,frame_4487_847_850 basis] at h
 exact h

theorem gate_851 : SixCarryPrefixData.program[851]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4626 4487 4488 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 83 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[83]?=some (.CCX 4626 4487 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[851]?=some (.CCX 4626 4487 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_851 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 852 basis 4488=((prefixState SixCarryPrefixData.program 0 basis 4488) ^^ ((prefixState SixCarryPrefixData.program 850 basis 4626) && (prefixState SixCarryPrefixData.program 851 basis 4487))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 851 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_851] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4488_0_851 basis,frame_4626_850_851 basis] at h
 exact h

theorem gate_852 : SixCarryPrefixData.program[852]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4488 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 84 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[84]?=some (.CX 4358 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[852]?=some (.CX 4358 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_852 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 853 basis 4488=((prefixState SixCarryPrefixData.program 852 basis 4488) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 852 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_852] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_852 basis] at h
 exact h

theorem gate_853 : SixCarryPrefixData.program[853]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4487 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 85 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[85]?=some (.CX 4358 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[853]?=some (.CX 4358 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_853 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 854 basis 4487=((prefixState SixCarryPrefixData.program 851 basis 4487) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 853 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_853] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_853 basis,frame_4487_851_853 basis] at h
 exact h

theorem gate_854 : SixCarryPrefixData.program[854]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4626 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 86 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[86]?=some (.CX 4358 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[854]?=some (.CX 4358 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_854 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 855 basis 4626=((prefixState SixCarryPrefixData.program 850 basis 4626) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 854 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_854] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_854 basis,frame_4626_850_854 basis] at h
 exact h

theorem gate_856 : SixCarryPrefixData.program[856]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4359 4488 := by
 have h := lookup_context SixCarryPrefixData.program before6 SixCarryPrefixData.chunk6 after6 768 88 shape6 before_len6 (by rw [len6]; decide +kernel)
 have hg : SixCarryPrefixData.chunk6[88]?=some (.CX 4359 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[856]?=some (.CX 4359 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_856 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 857 basis 4488=((prefixState SixCarryPrefixData.program 853 basis 4488) ^^ (prefixState SixCarryPrefixData.program 0 basis 4359)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 856 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_856] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4359_0_856 basis,frame_4488_853_856 basis] at h
 exact h

theorem gate_953 : SixCarryPrefixData.program[953]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4492 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 57 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[57]?=some (.measureX 4492 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[953]?=some (.measureX 4492 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_953 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 954 basis 4492=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 953 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4492
 rw [gate_953] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_956 : SixCarryPrefixData.program[956]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4491 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 60 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[60]?=some (.measureX 4491 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[956]?=some (.measureX 4491 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_956 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 957 basis 4491=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 956 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4491
 rw [gate_956] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_959 : SixCarryPrefixData.program[959]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4490 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 63 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[63]?=some (.measureX 4490 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[959]?=some (.measureX 4490 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_959 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 960 basis 4490=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 959 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4490
 rw [gate_959] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_962 : SixCarryPrefixData.program[962]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4489 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 66 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[66]?=some (.measureX 4489 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[962]?=some (.measureX 4489 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_962 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 963 basis 4489=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 962 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4489
 rw [gate_962] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_965 : SixCarryPrefixData.program[965]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4488 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 69 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[69]?=some (.measureX 4488 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[965]?=some (.measureX 4488 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_965 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 966 basis 4488=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 965 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_965] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_966 : SixCarryPrefixData.program[966]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4626 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 70 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[70]?=some (.CX 4358 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[966]?=some (.CX 4358 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_966 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 967 basis 4626=((prefixState SixCarryPrefixData.program 855 basis 4626) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 966 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_966] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_966 basis,frame_4626_855_966 basis] at h
 exact h

theorem gate_967 : SixCarryPrefixData.program[967]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4487 4626 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 71 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[71]?=some (.CX 4487 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[967]?=some (.CX 4487 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_967 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 968 basis 4626=((prefixState SixCarryPrefixData.program 967 basis 4626) ^^ (prefixState SixCarryPrefixData.program 854 basis 4487)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 967 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_967] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4487_854_967 basis] at h
 exact h

theorem gate_968 : SixCarryPrefixData.program[968]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4487 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 72 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[72]?=some (.measureX 4487 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[968]?=some (.measureX 4487 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_968 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 969 basis 4487=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 968 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_968] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_969 : SixCarryPrefixData.program[969]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4625 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 73 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[73]?=some (.CX 4357 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[969]?=some (.CX 4357 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_969 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 970 basis 4625=((prefixState SixCarryPrefixData.program 849 basis 4625) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 969 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_969] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_969 basis,frame_4625_849_969 basis] at h
 exact h

theorem gate_970 : SixCarryPrefixData.program[970]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4486 4625 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 74 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[74]?=some (.CX 4486 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[970]?=some (.CX 4486 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_970 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 971 basis 4625=((prefixState SixCarryPrefixData.program 970 basis 4625) ^^ (prefixState SixCarryPrefixData.program 848 basis 4486)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 970 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_970] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4486_848_970 basis] at h
 exact h

theorem gate_971 : SixCarryPrefixData.program[971]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4486 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 75 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[75]?=some (.measureX 4486 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[971]?=some (.measureX 4486 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_971 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 972 basis 4486=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 971 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_971] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_972 : SixCarryPrefixData.program[972]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4624 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 76 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[76]?=some (.CX 4356 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[972]?=some (.CX 4356 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_972 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 973 basis 4624=((prefixState SixCarryPrefixData.program 843 basis 4624) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 972 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_972] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_972 basis,frame_4624_843_972 basis] at h
 exact h

theorem gate_973 : SixCarryPrefixData.program[973]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4485 4624 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 77 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[77]?=some (.CX 4485 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[973]?=some (.CX 4485 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_973 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 974 basis 4624=((prefixState SixCarryPrefixData.program 973 basis 4624) ^^ (prefixState SixCarryPrefixData.program 842 basis 4485)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 973 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_973] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4485_842_973 basis] at h
 exact h

theorem gate_974 : SixCarryPrefixData.program[974]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4485 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 78 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[78]?=some (.measureX 4485 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[974]?=some (.measureX 4485 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_974 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 975 basis 4485=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 974 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_974] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_975 : SixCarryPrefixData.program[975]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4623 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 79 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[79]?=some (.CX 4355 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[975]?=some (.CX 4355 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_975 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 976 basis 4623=((prefixState SixCarryPrefixData.program 837 basis 4623) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 975 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_975] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_975 basis,frame_4623_837_975 basis] at h
 exact h

theorem gate_976 : SixCarryPrefixData.program[976]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4484 4623 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 80 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[80]?=some (.CX 4484 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[976]?=some (.CX 4484 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_976 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 977 basis 4623=((prefixState SixCarryPrefixData.program 976 basis 4623) ^^ (prefixState SixCarryPrefixData.program 836 basis 4484)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 976 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_976] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4484_836_976 basis] at h
 exact h

theorem gate_977 : SixCarryPrefixData.program[977]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4484 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 81 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[81]?=some (.measureX 4484 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[977]?=some (.measureX 4484 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_977 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 978 basis 4484=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 977 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_977] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_978 : SixCarryPrefixData.program[978]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4622 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 82 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[82]?=some (.CX 4354 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[978]?=some (.CX 4354 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_978 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 979 basis 4622=((prefixState SixCarryPrefixData.program 831 basis 4622) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 978 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_978] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_978 basis,frame_4622_831_978 basis] at h
 exact h

theorem gate_979 : SixCarryPrefixData.program[979]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4483 4622 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 83 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[83]?=some (.CX 4483 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[979]?=some (.CX 4483 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_979 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 980 basis 4622=((prefixState SixCarryPrefixData.program 979 basis 4622) ^^ (prefixState SixCarryPrefixData.program 830 basis 4483)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 979 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_979] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4483_830_979 basis] at h
 exact h

theorem gate_980 : SixCarryPrefixData.program[980]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4483 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 84 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[84]?=some (.measureX 4483 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[980]?=some (.measureX 4483 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_980 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 981 basis 4483=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 980 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_980] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_981 : SixCarryPrefixData.program[981]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4621 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 85 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[85]?=some (.CX 4353 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[981]?=some (.CX 4353 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_981 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 982 basis 4621=((prefixState SixCarryPrefixData.program 825 basis 4621) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 981 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_981] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_981 basis,frame_4621_825_981 basis] at h
 exact h

theorem gate_982 : SixCarryPrefixData.program[982]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4482 4621 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 86 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[86]?=some (.CX 4482 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[982]?=some (.CX 4482 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_982 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 983 basis 4621=((prefixState SixCarryPrefixData.program 982 basis 4621) ^^ (prefixState SixCarryPrefixData.program 824 basis 4482)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 982 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_982] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4482_824_982 basis] at h
 exact h

theorem gate_983 : SixCarryPrefixData.program[983]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4482 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 87 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[87]?=some (.measureX 4482 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[983]?=some (.measureX 4482 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_983 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 984 basis 4482=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 983 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_983] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_984 : SixCarryPrefixData.program[984]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4620 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 88 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[88]?=some (.CX 4352 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[984]?=some (.CX 4352 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_984 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 985 basis 4620=((prefixState SixCarryPrefixData.program 819 basis 4620) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 984 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_984] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_984 basis,frame_4620_819_984 basis] at h
 exact h

theorem gate_985 : SixCarryPrefixData.program[985]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4481 4620 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 89 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[89]?=some (.CX 4481 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[985]?=some (.CX 4481 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_985 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 986 basis 4620=((prefixState SixCarryPrefixData.program 985 basis 4620) ^^ (prefixState SixCarryPrefixData.program 818 basis 4481)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 985 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_985] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4481_818_985 basis] at h
 exact h

theorem gate_986 : SixCarryPrefixData.program[986]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4481 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 90 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[90]?=some (.measureX 4481 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[986]?=some (.measureX 4481 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_986 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 987 basis 4481=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 986 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_986] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_987 : SixCarryPrefixData.program[987]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4619 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 91 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[91]?=some (.CX 4351 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[987]?=some (.CX 4351 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_987 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 988 basis 4619=((prefixState SixCarryPrefixData.program 813 basis 4619) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 987 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_987] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_987 basis,frame_4619_813_987 basis] at h
 exact h

theorem gate_988 : SixCarryPrefixData.program[988]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4480 4619 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 92 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[92]?=some (.CX 4480 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[988]?=some (.CX 4480 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_988 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 989 basis 4619=((prefixState SixCarryPrefixData.program 988 basis 4619) ^^ (prefixState SixCarryPrefixData.program 812 basis 4480)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 988 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_988] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4480_812_988 basis] at h
 exact h

theorem gate_989 : SixCarryPrefixData.program[989]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4480 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 93 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[93]?=some (.measureX 4480 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[989]?=some (.measureX 4480 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_989 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 990 basis 4480=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 989 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_989] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_990 : SixCarryPrefixData.program[990]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4618 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 94 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[94]?=some (.CX 4350 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[990]?=some (.CX 4350 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_990 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 991 basis 4618=((prefixState SixCarryPrefixData.program 807 basis 4618) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 990 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_990] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_990 basis,frame_4618_807_990 basis] at h
 exact h

theorem gate_991 : SixCarryPrefixData.program[991]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4479 4618 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 95 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[95]?=some (.CX 4479 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[991]?=some (.CX 4479 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_991 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 992 basis 4618=((prefixState SixCarryPrefixData.program 991 basis 4618) ^^ (prefixState SixCarryPrefixData.program 806 basis 4479)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 991 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_991] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4479_806_991 basis] at h
 exact h

theorem gate_992 : SixCarryPrefixData.program[992]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4479 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 96 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[96]?=some (.measureX 4479 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[992]?=some (.measureX 4479 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_992 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 993 basis 4479=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 992 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_992] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_993 : SixCarryPrefixData.program[993]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4617 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 97 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[97]?=some (.CX 4349 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[993]?=some (.CX 4349 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_993 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 994 basis 4617=((prefixState SixCarryPrefixData.program 801 basis 4617) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 993 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_993] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_993 basis,frame_4617_801_993 basis] at h
 exact h

theorem gate_994 : SixCarryPrefixData.program[994]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4478 4617 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 98 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[98]?=some (.CX 4478 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[994]?=some (.CX 4478 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_994 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 995 basis 4617=((prefixState SixCarryPrefixData.program 994 basis 4617) ^^ (prefixState SixCarryPrefixData.program 800 basis 4478)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 994 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_994] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4478_800_994 basis] at h
 exact h

theorem gate_995 : SixCarryPrefixData.program[995]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4478 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 99 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[99]?=some (.measureX 4478 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[995]?=some (.measureX 4478 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_995 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 996 basis 4478=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 995 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_995] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_996 : SixCarryPrefixData.program[996]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4616 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 100 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[100]?=some (.CX 4348 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[996]?=some (.CX 4348 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_996 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 997 basis 4616=((prefixState SixCarryPrefixData.program 795 basis 4616) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 996 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_996] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_996 basis,frame_4616_795_996 basis] at h
 exact h

theorem gate_997 : SixCarryPrefixData.program[997]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4477 4616 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 101 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[101]?=some (.CX 4477 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[997]?=some (.CX 4477 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_997 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 998 basis 4616=((prefixState SixCarryPrefixData.program 997 basis 4616) ^^ (prefixState SixCarryPrefixData.program 794 basis 4477)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 997 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_997] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4477_794_997 basis] at h
 exact h

theorem gate_998 : SixCarryPrefixData.program[998]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4477 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 102 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[102]?=some (.measureX 4477 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[998]?=some (.measureX 4477 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_998 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 999 basis 4477=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 998 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_998] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_999 : SixCarryPrefixData.program[999]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4615 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 103 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[103]?=some (.CX 4347 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[999]?=some (.CX 4347 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_999 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1000 basis 4615=((prefixState SixCarryPrefixData.program 789 basis 4615) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 999 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_999] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_999 basis,frame_4615_789_999 basis] at h
 exact h

theorem gate_1000 : SixCarryPrefixData.program[1000]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4476 4615 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 104 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[104]?=some (.CX 4476 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[1000]?=some (.CX 4476 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1000 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1001 basis 4615=((prefixState SixCarryPrefixData.program 1000 basis 4615) ^^ (prefixState SixCarryPrefixData.program 788 basis 4476)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1000 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_1000] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4476_788_1000 basis] at h
 exact h

theorem gate_1001 : SixCarryPrefixData.program[1001]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4476 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 105 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[105]?=some (.measureX 4476 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[1001]?=some (.measureX 4476 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1001 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1002 basis 4476=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1001 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_1001] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_1002 : SixCarryPrefixData.program[1002]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4614 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 106 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[106]?=some (.CX 4346 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[1002]?=some (.CX 4346 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1002 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1003 basis 4614=((prefixState SixCarryPrefixData.program 783 basis 4614) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1002 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_1002] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_1002 basis,frame_4614_783_1002 basis] at h
 exact h

theorem gate_1003 : SixCarryPrefixData.program[1003]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4475 4614 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 107 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[107]?=some (.CX 4475 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[1003]?=some (.CX 4475 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1003 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1004 basis 4614=((prefixState SixCarryPrefixData.program 1003 basis 4614) ^^ (prefixState SixCarryPrefixData.program 782 basis 4475)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1003 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_1003] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4475_782_1003 basis] at h
 exact h

theorem gate_1004 : SixCarryPrefixData.program[1004]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4475 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 108 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[108]?=some (.measureX 4475 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[1004]?=some (.measureX 4475 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1004 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1005 basis 4475=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1004 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_1004] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_1005 : SixCarryPrefixData.program[1005]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4613 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 109 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[109]?=some (.CX 4345 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[1005]?=some (.CX 4345 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1005 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1006 basis 4613=((prefixState SixCarryPrefixData.program 777 basis 4613) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1005 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_1005] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_1005 basis,frame_4613_777_1005 basis] at h
 exact h

theorem gate_1006 : SixCarryPrefixData.program[1006]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4474 4613 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 110 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[110]?=some (.CX 4474 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[1006]?=some (.CX 4474 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1006 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1007 basis 4613=((prefixState SixCarryPrefixData.program 1006 basis 4613) ^^ (prefixState SixCarryPrefixData.program 776 basis 4474)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1006 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_1006] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4474_776_1006 basis] at h
 exact h

theorem gate_1007 : SixCarryPrefixData.program[1007]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.measureX 4474 [] [] := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 111 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[111]?=some (.measureX 4474 [] []) := by decide +kernel
 have hh : SixCarryPrefixData.program[1007]?=some (.measureX 4474 [] []) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1007 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1008 basis 4474=(false) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1007 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_1007] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 exact h

theorem gate_1008 : SixCarryPrefixData.program[1008]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4612 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 112 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[112]?=some (.CX 4344 4612) := by decide +kernel
 have hh : SixCarryPrefixData.program[1008]?=some (.CX 4344 4612) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1008 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1009 basis 4612=((prefixState SixCarryPrefixData.program 771 basis 4612) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1008 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4612
 rw [gate_1008] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_1008 basis,frame_4612_771_1008 basis] at h
 exact h

theorem gate_1009 : SixCarryPrefixData.program[1009]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4473 4612 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 113 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[113]?=some (.CX 4473 4612) := by decide +kernel
 have hh : SixCarryPrefixData.program[1009]?=some (.CX 4473 4612) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1009 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1010 basis 4612=((prefixState SixCarryPrefixData.program 1009 basis 4612) ^^ (prefixState SixCarryPrefixData.program 770 basis 4473)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1009 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4612
 rw [gate_1009] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4473_770_1009 basis] at h
 exact h

theorem gate_1017 : SixCarryPrefixData.program[1017]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4341 4609 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 121 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[121]?=some (.CX 4341 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[1017]?=some (.CX 4341 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1017 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1018 basis 4609=((prefixState SixCarryPrefixData.program 753 basis 4609) ^^ (prefixState SixCarryPrefixData.program 0 basis 4341)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1017 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_1017] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4341_0_1017 basis,frame_4609_753_1017 basis] at h
 exact h

theorem gate_1018 : SixCarryPrefixData.program[1018]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4470 4609 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 122 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[122]?=some (.CX 4470 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[1018]?=some (.CX 4470 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1018 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1019 basis 4609=((prefixState SixCarryPrefixData.program 1018 basis 4609) ^^ (prefixState SixCarryPrefixData.program 752 basis 4470)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1018 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_1018] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4470_752_1018 basis] at h
 exact h

theorem gate_1020 : SixCarryPrefixData.program[1020]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4340 4608 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 124 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[124]?=some (.CX 4340 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[1020]?=some (.CX 4340 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1020 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1021 basis 4608=((prefixState SixCarryPrefixData.program 747 basis 4608) ^^ (prefixState SixCarryPrefixData.program 0 basis 4340)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1020 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_1020] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4340_0_1020 basis,frame_4608_747_1020 basis] at h
 exact h

theorem gate_1021 : SixCarryPrefixData.program[1021]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4469 4608 := by
 have h := lookup_context SixCarryPrefixData.program before7 SixCarryPrefixData.chunk7 after7 896 125 shape7 before_len7 (by rw [len7]; decide +kernel)
 have hg : SixCarryPrefixData.chunk7[125]?=some (.CX 4469 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[1021]?=some (.CX 4469 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1021 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1022 basis 4608=((prefixState SixCarryPrefixData.program 1021 basis 4608) ^^ (prefixState SixCarryPrefixData.program 746 basis 4469)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1021 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_1021] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4469_746_1021 basis] at h
 exact h

theorem gate_1414 : SixCarryPrefixData.program[1414]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4608 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 6 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[6]?=some (.X 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[1414]?=some (.X 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1414 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1415 basis 4608=(!(prefixState SixCarryPrefixData.program 1022 basis 4608)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1414 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_1414] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4608_1022_1414 basis] at h
 exact h

theorem gate_1415 : SixCarryPrefixData.program[1415]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4609 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 7 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[7]?=some (.X 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[1415]?=some (.X 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1415 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1416 basis 4609=(!(prefixState SixCarryPrefixData.program 1019 basis 4609)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1415 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_1415] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4609_1019_1415 basis] at h
 exact h

theorem gate_1418 : SixCarryPrefixData.program[1418]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4612 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 10 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[10]?=some (.X 4612) := by decide +kernel
 have hh : SixCarryPrefixData.program[1418]?=some (.X 4612) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1418 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1419 basis 4612=(!(prefixState SixCarryPrefixData.program 1010 basis 4612)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1418 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4612
 rw [gate_1418] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4612_1010_1418 basis] at h
 exact h

theorem gate_1419 : SixCarryPrefixData.program[1419]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4613 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 11 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[11]?=some (.X 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[1419]?=some (.X 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1419 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1420 basis 4613=(!(prefixState SixCarryPrefixData.program 1007 basis 4613)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1419 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_1419] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4613_1007_1419 basis] at h
 exact h

theorem gate_1420 : SixCarryPrefixData.program[1420]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4614 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 12 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[12]?=some (.X 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[1420]?=some (.X 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1420 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1421 basis 4614=(!(prefixState SixCarryPrefixData.program 1004 basis 4614)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1420 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_1420] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4614_1004_1420 basis] at h
 exact h

theorem gate_1421 : SixCarryPrefixData.program[1421]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4615 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 13 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[13]?=some (.X 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[1421]?=some (.X 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1421 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1422 basis 4615=(!(prefixState SixCarryPrefixData.program 1001 basis 4615)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1421 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_1421] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4615_1001_1421 basis] at h
 exact h

theorem gate_1422 : SixCarryPrefixData.program[1422]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4616 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 14 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[14]?=some (.X 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[1422]?=some (.X 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1422 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1423 basis 4616=(!(prefixState SixCarryPrefixData.program 998 basis 4616)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1422 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_1422] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4616_998_1422 basis] at h
 exact h

theorem gate_1423 : SixCarryPrefixData.program[1423]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4617 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 15 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[15]?=some (.X 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[1423]?=some (.X 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1423 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1424 basis 4617=(!(prefixState SixCarryPrefixData.program 995 basis 4617)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1423 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_1423] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4617_995_1423 basis] at h
 exact h

theorem gate_1424 : SixCarryPrefixData.program[1424]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4618 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 16 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[16]?=some (.X 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[1424]?=some (.X 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1424 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1425 basis 4618=(!(prefixState SixCarryPrefixData.program 992 basis 4618)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1424 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_1424] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4618_992_1424 basis] at h
 exact h

theorem gate_1425 : SixCarryPrefixData.program[1425]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4619 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 17 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[17]?=some (.X 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[1425]?=some (.X 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1425 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1426 basis 4619=(!(prefixState SixCarryPrefixData.program 989 basis 4619)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1425 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_1425] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4619_989_1425 basis] at h
 exact h

theorem gate_1426 : SixCarryPrefixData.program[1426]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4620 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 18 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[18]?=some (.X 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[1426]?=some (.X 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1426 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1427 basis 4620=(!(prefixState SixCarryPrefixData.program 986 basis 4620)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1426 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_1426] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4620_986_1426 basis] at h
 exact h

theorem gate_1427 : SixCarryPrefixData.program[1427]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4621 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 19 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[19]?=some (.X 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[1427]?=some (.X 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1427 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1428 basis 4621=(!(prefixState SixCarryPrefixData.program 983 basis 4621)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1427 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_1427] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4621_983_1427 basis] at h
 exact h

theorem gate_1428 : SixCarryPrefixData.program[1428]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4622 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 20 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[20]?=some (.X 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[1428]?=some (.X 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1428 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1429 basis 4622=(!(prefixState SixCarryPrefixData.program 980 basis 4622)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1428 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_1428] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4622_980_1428 basis] at h
 exact h

theorem gate_1429 : SixCarryPrefixData.program[1429]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4623 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 21 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[21]?=some (.X 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[1429]?=some (.X 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1429 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1430 basis 4623=(!(prefixState SixCarryPrefixData.program 977 basis 4623)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1429 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_1429] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4623_977_1429 basis] at h
 exact h

theorem gate_1430 : SixCarryPrefixData.program[1430]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4624 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 22 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[22]?=some (.X 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[1430]?=some (.X 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1430 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1431 basis 4624=(!(prefixState SixCarryPrefixData.program 974 basis 4624)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1430 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_1430] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4624_974_1430 basis] at h
 exact h

theorem gate_1431 : SixCarryPrefixData.program[1431]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4625 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 23 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[23]?=some (.X 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[1431]?=some (.X 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1431 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1432 basis 4625=(!(prefixState SixCarryPrefixData.program 971 basis 4625)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1431 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_1431] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4625_971_1431 basis] at h
 exact h

theorem gate_1432 : SixCarryPrefixData.program[1432]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.X 4626 := by
 have h := lookup_context SixCarryPrefixData.program before11 SixCarryPrefixData.chunk11 after11 1408 24 shape11 before_len11 (by rw [len11]; decide +kernel)
 have hg : SixCarryPrefixData.chunk11[24]?=some (.X 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[1432]?=some (.X 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_1432 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 1433 basis 4626=(!(prefixState SixCarryPrefixData.program 968 basis 4626)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 1432 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_1432] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4626_968_1432 basis] at h
 exact h

theorem gate_2141 : SixCarryPrefixData.program[2141]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4608 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 93 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[93]?=some (.CX 4344 4608) := by decide +kernel
 have hh : SixCarryPrefixData.program[2141]?=some (.CX 4344 4608) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2141 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2142 basis 4608=((prefixState SixCarryPrefixData.program 1415 basis 4608) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2141 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4608
 rw [gate_2141] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_2141 basis,frame_4608_1415_2141 basis] at h
 exact h

theorem gate_2143 : SixCarryPrefixData.program[2143]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4608 4473 4474 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 95 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[95]?=some (.CCX 4608 4473 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[2143]?=some (.CCX 4608 4473 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2143 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2144 basis 4474=((prefixState SixCarryPrefixData.program 1008 basis 4474) ^^ ((prefixState SixCarryPrefixData.program 2142 basis 4608) && (prefixState SixCarryPrefixData.program 2143 basis 4473))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2143 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_2143] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4474_1008_2143 basis,frame_4608_2142_2143 basis] at h
 exact h

theorem gate_2144 : SixCarryPrefixData.program[2144]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4344 4474 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 96 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[96]?=some (.CX 4344 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[2144]?=some (.CX 4344 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2144 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2145 basis 4474=((prefixState SixCarryPrefixData.program 2144 basis 4474) ^^ (prefixState SixCarryPrefixData.program 0 basis 4344)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2144 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_2144] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4344_0_2144 basis] at h
 exact h

theorem gate_2147 : SixCarryPrefixData.program[2147]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4609 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 99 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[99]?=some (.CX 4345 4609) := by decide +kernel
 have hh : SixCarryPrefixData.program[2147]?=some (.CX 4345 4609) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2147 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2148 basis 4609=((prefixState SixCarryPrefixData.program 1416 basis 4609) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2147 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4609
 rw [gate_2147] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_2147 basis,frame_4609_1416_2147 basis] at h
 exact h

theorem gate_2148 : SixCarryPrefixData.program[2148]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4474 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 100 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[100]?=some (.CX 4345 4474) := by decide +kernel
 have hh : SixCarryPrefixData.program[2148]?=some (.CX 4345 4474) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2148 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2149 basis 4474=((prefixState SixCarryPrefixData.program 2145 basis 4474) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2148 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4474
 rw [gate_2148] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_2148 basis,frame_4474_2145_2148 basis] at h
 exact h

theorem gate_2149 : SixCarryPrefixData.program[2149]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4609 4474 4475 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 101 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[101]?=some (.CCX 4609 4474 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[2149]?=some (.CCX 4609 4474 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2149 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2150 basis 4475=((prefixState SixCarryPrefixData.program 1005 basis 4475) ^^ ((prefixState SixCarryPrefixData.program 2148 basis 4609) && (prefixState SixCarryPrefixData.program 2149 basis 4474))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2149 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_2149] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4475_1005_2149 basis,frame_4609_2148_2149 basis] at h
 exact h

theorem gate_2150 : SixCarryPrefixData.program[2150]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4345 4475 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 102 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[102]?=some (.CX 4345 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[2150]?=some (.CX 4345 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2150 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2151 basis 4475=((prefixState SixCarryPrefixData.program 2150 basis 4475) ^^ (prefixState SixCarryPrefixData.program 0 basis 4345)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2150 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_2150] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4345_0_2150 basis] at h
 exact h

theorem gate_2154 : SixCarryPrefixData.program[2154]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4475 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 106 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[106]?=some (.CX 4346 4475) := by decide +kernel
 have hh : SixCarryPrefixData.program[2154]?=some (.CX 4346 4475) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2154 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2155 basis 4475=((prefixState SixCarryPrefixData.program 2151 basis 4475) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2154 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4475
 rw [gate_2154] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_2154 basis,frame_4475_2151_2154 basis] at h
 exact h

theorem gate_2155 : SixCarryPrefixData.program[2155]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4610 4475 4476 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 107 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[107]?=some (.CCX 4610 4475 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[2155]?=some (.CCX 4610 4475 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2155 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2156 basis 4476=((prefixState SixCarryPrefixData.program 1002 basis 4476) ^^ ((prefixState SixCarryPrefixData.program 2154 basis 4610) && (prefixState SixCarryPrefixData.program 2155 basis 4475))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2155 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_2155] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4476_1002_2155 basis,frame_4610_2154_2155 basis] at h
 exact h

theorem gate_2156 : SixCarryPrefixData.program[2156]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4346 4476 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 108 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[108]?=some (.CX 4346 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[2156]?=some (.CX 4346 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2156 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2157 basis 4476=((prefixState SixCarryPrefixData.program 2156 basis 4476) ^^ (prefixState SixCarryPrefixData.program 0 basis 4346)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2156 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_2156] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4346_0_2156 basis] at h
 exact h

theorem gate_2160 : SixCarryPrefixData.program[2160]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4476 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 112 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[112]?=some (.CX 4347 4476) := by decide +kernel
 have hh : SixCarryPrefixData.program[2160]?=some (.CX 4347 4476) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2160 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2161 basis 4476=((prefixState SixCarryPrefixData.program 2157 basis 4476) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2160 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4476
 rw [gate_2160] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_2160 basis,frame_4476_2157_2160 basis] at h
 exact h

theorem gate_2161 : SixCarryPrefixData.program[2161]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4611 4476 4477 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 113 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[113]?=some (.CCX 4611 4476 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[2161]?=some (.CCX 4611 4476 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2161 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2162 basis 4477=((prefixState SixCarryPrefixData.program 999 basis 4477) ^^ ((prefixState SixCarryPrefixData.program 2160 basis 4611) && (prefixState SixCarryPrefixData.program 2161 basis 4476))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2161 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_2161] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4477_999_2161 basis,frame_4611_2160_2161 basis] at h
 exact h

theorem gate_2162 : SixCarryPrefixData.program[2162]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4347 4477 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 114 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[114]?=some (.CX 4347 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[2162]?=some (.CX 4347 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2162 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2163 basis 4477=((prefixState SixCarryPrefixData.program 2162 basis 4477) ^^ (prefixState SixCarryPrefixData.program 0 basis 4347)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2162 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_2162] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4347_0_2162 basis] at h
 exact h

theorem gate_2165 : SixCarryPrefixData.program[2165]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4612 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 117 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[117]?=some (.CX 4348 4612) := by decide +kernel
 have hh : SixCarryPrefixData.program[2165]?=some (.CX 4348 4612) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2165 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2166 basis 4612=((prefixState SixCarryPrefixData.program 1419 basis 4612) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2165 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4612
 rw [gate_2165] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_2165 basis,frame_4612_1419_2165 basis] at h
 exact h

theorem gate_2166 : SixCarryPrefixData.program[2166]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4477 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 118 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[118]?=some (.CX 4348 4477) := by decide +kernel
 have hh : SixCarryPrefixData.program[2166]?=some (.CX 4348 4477) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2166 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2167 basis 4477=((prefixState SixCarryPrefixData.program 2163 basis 4477) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2166 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4477
 rw [gate_2166] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_2166 basis,frame_4477_2163_2166 basis] at h
 exact h

theorem gate_2167 : SixCarryPrefixData.program[2167]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4612 4477 4478 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 119 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[119]?=some (.CCX 4612 4477 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[2167]?=some (.CCX 4612 4477 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2167 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2168 basis 4478=((prefixState SixCarryPrefixData.program 996 basis 4478) ^^ ((prefixState SixCarryPrefixData.program 2166 basis 4612) && (prefixState SixCarryPrefixData.program 2167 basis 4477))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2167 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_2167] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4478_996_2167 basis,frame_4612_2166_2167 basis] at h
 exact h

theorem gate_2168 : SixCarryPrefixData.program[2168]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4348 4478 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 120 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[120]?=some (.CX 4348 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[2168]?=some (.CX 4348 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2168 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2169 basis 4478=((prefixState SixCarryPrefixData.program 2168 basis 4478) ^^ (prefixState SixCarryPrefixData.program 0 basis 4348)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2168 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_2168] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4348_0_2168 basis] at h
 exact h

theorem gate_2171 : SixCarryPrefixData.program[2171]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4613 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 123 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[123]?=some (.CX 4349 4613) := by decide +kernel
 have hh : SixCarryPrefixData.program[2171]?=some (.CX 4349 4613) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2171 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2172 basis 4613=((prefixState SixCarryPrefixData.program 1420 basis 4613) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2171 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4613
 rw [gate_2171] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_2171 basis,frame_4613_1420_2171 basis] at h
 exact h

theorem gate_2172 : SixCarryPrefixData.program[2172]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4478 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 124 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[124]?=some (.CX 4349 4478) := by decide +kernel
 have hh : SixCarryPrefixData.program[2172]?=some (.CX 4349 4478) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2172 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2173 basis 4478=((prefixState SixCarryPrefixData.program 2169 basis 4478) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2172 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4478
 rw [gate_2172] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_2172 basis,frame_4478_2169_2172 basis] at h
 exact h

theorem gate_2173 : SixCarryPrefixData.program[2173]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4613 4478 4479 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 125 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[125]?=some (.CCX 4613 4478 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[2173]?=some (.CCX 4613 4478 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2173 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2174 basis 4479=((prefixState SixCarryPrefixData.program 993 basis 4479) ^^ ((prefixState SixCarryPrefixData.program 2172 basis 4613) && (prefixState SixCarryPrefixData.program 2173 basis 4478))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2173 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_2173] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4479_993_2173 basis,frame_4613_2172_2173 basis] at h
 exact h

theorem gate_2174 : SixCarryPrefixData.program[2174]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4349 4479 := by
 have h := lookup_context SixCarryPrefixData.program before16 SixCarryPrefixData.chunk16 after16 2048 126 shape16 before_len16 (by rw [len16]; decide +kernel)
 have hg : SixCarryPrefixData.chunk16[126]?=some (.CX 4349 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[2174]?=some (.CX 4349 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2174 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2175 basis 4479=((prefixState SixCarryPrefixData.program 2174 basis 4479) ^^ (prefixState SixCarryPrefixData.program 0 basis 4349)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2174 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_2174] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4349_0_2174 basis] at h
 exact h

theorem gate_2177 : SixCarryPrefixData.program[2177]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4614 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 1 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[1]?=some (.CX 4350 4614) := by decide +kernel
 have hh : SixCarryPrefixData.program[2177]?=some (.CX 4350 4614) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2177 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2178 basis 4614=((prefixState SixCarryPrefixData.program 1421 basis 4614) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2177 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4614
 rw [gate_2177] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_2177 basis,frame_4614_1421_2177 basis] at h
 exact h

theorem gate_2178 : SixCarryPrefixData.program[2178]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4479 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 2 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[2]?=some (.CX 4350 4479) := by decide +kernel
 have hh : SixCarryPrefixData.program[2178]?=some (.CX 4350 4479) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2178 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2179 basis 4479=((prefixState SixCarryPrefixData.program 2175 basis 4479) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2178 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4479
 rw [gate_2178] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_2178 basis,frame_4479_2175_2178 basis] at h
 exact h

theorem gate_2179 : SixCarryPrefixData.program[2179]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4614 4479 4480 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 3 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[3]?=some (.CCX 4614 4479 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[2179]?=some (.CCX 4614 4479 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2179 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2180 basis 4480=((prefixState SixCarryPrefixData.program 990 basis 4480) ^^ ((prefixState SixCarryPrefixData.program 2178 basis 4614) && (prefixState SixCarryPrefixData.program 2179 basis 4479))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2179 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_2179] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4480_990_2179 basis,frame_4614_2178_2179 basis] at h
 exact h

theorem gate_2180 : SixCarryPrefixData.program[2180]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4350 4480 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 4 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[4]?=some (.CX 4350 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[2180]?=some (.CX 4350 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2180 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2181 basis 4480=((prefixState SixCarryPrefixData.program 2180 basis 4480) ^^ (prefixState SixCarryPrefixData.program 0 basis 4350)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2180 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_2180] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4350_0_2180 basis] at h
 exact h

theorem gate_2183 : SixCarryPrefixData.program[2183]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4615 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 7 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[7]?=some (.CX 4351 4615) := by decide +kernel
 have hh : SixCarryPrefixData.program[2183]?=some (.CX 4351 4615) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2183 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2184 basis 4615=((prefixState SixCarryPrefixData.program 1422 basis 4615) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2183 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4615
 rw [gate_2183] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_2183 basis,frame_4615_1422_2183 basis] at h
 exact h

theorem gate_2184 : SixCarryPrefixData.program[2184]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4480 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 8 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[8]?=some (.CX 4351 4480) := by decide +kernel
 have hh : SixCarryPrefixData.program[2184]?=some (.CX 4351 4480) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2184 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2185 basis 4480=((prefixState SixCarryPrefixData.program 2181 basis 4480) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2184 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4480
 rw [gate_2184] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_2184 basis,frame_4480_2181_2184 basis] at h
 exact h

theorem gate_2185 : SixCarryPrefixData.program[2185]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4615 4480 4481 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 9 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[9]?=some (.CCX 4615 4480 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[2185]?=some (.CCX 4615 4480 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2185 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2186 basis 4481=((prefixState SixCarryPrefixData.program 987 basis 4481) ^^ ((prefixState SixCarryPrefixData.program 2184 basis 4615) && (prefixState SixCarryPrefixData.program 2185 basis 4480))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2185 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_2185] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4481_987_2185 basis,frame_4615_2184_2185 basis] at h
 exact h

theorem gate_2186 : SixCarryPrefixData.program[2186]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4351 4481 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 10 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[10]?=some (.CX 4351 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[2186]?=some (.CX 4351 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2186 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2187 basis 4481=((prefixState SixCarryPrefixData.program 2186 basis 4481) ^^ (prefixState SixCarryPrefixData.program 0 basis 4351)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2186 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_2186] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4351_0_2186 basis] at h
 exact h

theorem gate_2189 : SixCarryPrefixData.program[2189]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4616 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 13 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[13]?=some (.CX 4352 4616) := by decide +kernel
 have hh : SixCarryPrefixData.program[2189]?=some (.CX 4352 4616) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2189 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2190 basis 4616=((prefixState SixCarryPrefixData.program 1423 basis 4616) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2189 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4616
 rw [gate_2189] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_2189 basis,frame_4616_1423_2189 basis] at h
 exact h

theorem gate_2190 : SixCarryPrefixData.program[2190]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4481 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 14 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[14]?=some (.CX 4352 4481) := by decide +kernel
 have hh : SixCarryPrefixData.program[2190]?=some (.CX 4352 4481) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2190 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2191 basis 4481=((prefixState SixCarryPrefixData.program 2187 basis 4481) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2190 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4481
 rw [gate_2190] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_2190 basis,frame_4481_2187_2190 basis] at h
 exact h

theorem gate_2191 : SixCarryPrefixData.program[2191]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4616 4481 4482 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 15 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[15]?=some (.CCX 4616 4481 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[2191]?=some (.CCX 4616 4481 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2191 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2192 basis 4482=((prefixState SixCarryPrefixData.program 984 basis 4482) ^^ ((prefixState SixCarryPrefixData.program 2190 basis 4616) && (prefixState SixCarryPrefixData.program 2191 basis 4481))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2191 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_2191] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4482_984_2191 basis,frame_4616_2190_2191 basis] at h
 exact h

theorem gate_2192 : SixCarryPrefixData.program[2192]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4352 4482 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 16 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[16]?=some (.CX 4352 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[2192]?=some (.CX 4352 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2192 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2193 basis 4482=((prefixState SixCarryPrefixData.program 2192 basis 4482) ^^ (prefixState SixCarryPrefixData.program 0 basis 4352)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2192 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_2192] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4352_0_2192 basis] at h
 exact h

theorem gate_2195 : SixCarryPrefixData.program[2195]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4617 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 19 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[19]?=some (.CX 4353 4617) := by decide +kernel
 have hh : SixCarryPrefixData.program[2195]?=some (.CX 4353 4617) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2195 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2196 basis 4617=((prefixState SixCarryPrefixData.program 1424 basis 4617) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2195 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4617
 rw [gate_2195] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_2195 basis,frame_4617_1424_2195 basis] at h
 exact h

theorem gate_2196 : SixCarryPrefixData.program[2196]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4482 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 20 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[20]?=some (.CX 4353 4482) := by decide +kernel
 have hh : SixCarryPrefixData.program[2196]?=some (.CX 4353 4482) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2196 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2197 basis 4482=((prefixState SixCarryPrefixData.program 2193 basis 4482) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2196 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4482
 rw [gate_2196] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_2196 basis,frame_4482_2193_2196 basis] at h
 exact h

theorem gate_2197 : SixCarryPrefixData.program[2197]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4617 4482 4483 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 21 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[21]?=some (.CCX 4617 4482 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[2197]?=some (.CCX 4617 4482 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2197 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2198 basis 4483=((prefixState SixCarryPrefixData.program 981 basis 4483) ^^ ((prefixState SixCarryPrefixData.program 2196 basis 4617) && (prefixState SixCarryPrefixData.program 2197 basis 4482))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2197 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_2197] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4483_981_2197 basis,frame_4617_2196_2197 basis] at h
 exact h

theorem gate_2198 : SixCarryPrefixData.program[2198]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4353 4483 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 22 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[22]?=some (.CX 4353 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[2198]?=some (.CX 4353 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2198 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2199 basis 4483=((prefixState SixCarryPrefixData.program 2198 basis 4483) ^^ (prefixState SixCarryPrefixData.program 0 basis 4353)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2198 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_2198] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4353_0_2198 basis] at h
 exact h

theorem gate_2201 : SixCarryPrefixData.program[2201]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4618 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 25 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[25]?=some (.CX 4354 4618) := by decide +kernel
 have hh : SixCarryPrefixData.program[2201]?=some (.CX 4354 4618) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2201 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2202 basis 4618=((prefixState SixCarryPrefixData.program 1425 basis 4618) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2201 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4618
 rw [gate_2201] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_2201 basis,frame_4618_1425_2201 basis] at h
 exact h

theorem gate_2202 : SixCarryPrefixData.program[2202]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4483 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 26 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[26]?=some (.CX 4354 4483) := by decide +kernel
 have hh : SixCarryPrefixData.program[2202]?=some (.CX 4354 4483) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2202 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2203 basis 4483=((prefixState SixCarryPrefixData.program 2199 basis 4483) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2202 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4483
 rw [gate_2202] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_2202 basis,frame_4483_2199_2202 basis] at h
 exact h

theorem gate_2203 : SixCarryPrefixData.program[2203]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4618 4483 4484 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 27 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[27]?=some (.CCX 4618 4483 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[2203]?=some (.CCX 4618 4483 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2203 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2204 basis 4484=((prefixState SixCarryPrefixData.program 978 basis 4484) ^^ ((prefixState SixCarryPrefixData.program 2202 basis 4618) && (prefixState SixCarryPrefixData.program 2203 basis 4483))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2203 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_2203] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4484_978_2203 basis,frame_4618_2202_2203 basis] at h
 exact h

theorem gate_2204 : SixCarryPrefixData.program[2204]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4354 4484 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 28 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[28]?=some (.CX 4354 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[2204]?=some (.CX 4354 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2204 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2205 basis 4484=((prefixState SixCarryPrefixData.program 2204 basis 4484) ^^ (prefixState SixCarryPrefixData.program 0 basis 4354)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2204 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_2204] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4354_0_2204 basis] at h
 exact h

theorem gate_2207 : SixCarryPrefixData.program[2207]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4619 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 31 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[31]?=some (.CX 4355 4619) := by decide +kernel
 have hh : SixCarryPrefixData.program[2207]?=some (.CX 4355 4619) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2207 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2208 basis 4619=((prefixState SixCarryPrefixData.program 1426 basis 4619) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2207 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4619
 rw [gate_2207] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_2207 basis,frame_4619_1426_2207 basis] at h
 exact h

theorem gate_2208 : SixCarryPrefixData.program[2208]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4484 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 32 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[32]?=some (.CX 4355 4484) := by decide +kernel
 have hh : SixCarryPrefixData.program[2208]?=some (.CX 4355 4484) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2208 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2209 basis 4484=((prefixState SixCarryPrefixData.program 2205 basis 4484) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2208 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4484
 rw [gate_2208] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_2208 basis,frame_4484_2205_2208 basis] at h
 exact h

theorem gate_2209 : SixCarryPrefixData.program[2209]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4619 4484 4485 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 33 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[33]?=some (.CCX 4619 4484 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[2209]?=some (.CCX 4619 4484 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2209 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2210 basis 4485=((prefixState SixCarryPrefixData.program 975 basis 4485) ^^ ((prefixState SixCarryPrefixData.program 2208 basis 4619) && (prefixState SixCarryPrefixData.program 2209 basis 4484))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2209 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_2209] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4485_975_2209 basis,frame_4619_2208_2209 basis] at h
 exact h

theorem gate_2210 : SixCarryPrefixData.program[2210]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4355 4485 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 34 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[34]?=some (.CX 4355 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[2210]?=some (.CX 4355 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2210 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2211 basis 4485=((prefixState SixCarryPrefixData.program 2210 basis 4485) ^^ (prefixState SixCarryPrefixData.program 0 basis 4355)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2210 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_2210] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4355_0_2210 basis] at h
 exact h

theorem gate_2213 : SixCarryPrefixData.program[2213]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4620 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 37 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[37]?=some (.CX 4356 4620) := by decide +kernel
 have hh : SixCarryPrefixData.program[2213]?=some (.CX 4356 4620) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2213 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2214 basis 4620=((prefixState SixCarryPrefixData.program 1427 basis 4620) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2213 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4620
 rw [gate_2213] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_2213 basis,frame_4620_1427_2213 basis] at h
 exact h

theorem gate_2214 : SixCarryPrefixData.program[2214]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4485 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 38 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[38]?=some (.CX 4356 4485) := by decide +kernel
 have hh : SixCarryPrefixData.program[2214]?=some (.CX 4356 4485) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2214 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2215 basis 4485=((prefixState SixCarryPrefixData.program 2211 basis 4485) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2214 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4485
 rw [gate_2214] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_2214 basis,frame_4485_2211_2214 basis] at h
 exact h

theorem gate_2215 : SixCarryPrefixData.program[2215]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4620 4485 4486 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 39 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[39]?=some (.CCX 4620 4485 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[2215]?=some (.CCX 4620 4485 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2215 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2216 basis 4486=((prefixState SixCarryPrefixData.program 972 basis 4486) ^^ ((prefixState SixCarryPrefixData.program 2214 basis 4620) && (prefixState SixCarryPrefixData.program 2215 basis 4485))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2215 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_2215] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4486_972_2215 basis,frame_4620_2214_2215 basis] at h
 exact h

theorem gate_2216 : SixCarryPrefixData.program[2216]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4356 4486 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 40 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[40]?=some (.CX 4356 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[2216]?=some (.CX 4356 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2216 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2217 basis 4486=((prefixState SixCarryPrefixData.program 2216 basis 4486) ^^ (prefixState SixCarryPrefixData.program 0 basis 4356)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2216 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_2216] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4356_0_2216 basis] at h
 exact h

theorem gate_2219 : SixCarryPrefixData.program[2219]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4621 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 43 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[43]?=some (.CX 4357 4621) := by decide +kernel
 have hh : SixCarryPrefixData.program[2219]?=some (.CX 4357 4621) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2219 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2220 basis 4621=((prefixState SixCarryPrefixData.program 1428 basis 4621) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2219 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4621
 rw [gate_2219] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_2219 basis,frame_4621_1428_2219 basis] at h
 exact h

theorem gate_2220 : SixCarryPrefixData.program[2220]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4486 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 44 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[44]?=some (.CX 4357 4486) := by decide +kernel
 have hh : SixCarryPrefixData.program[2220]?=some (.CX 4357 4486) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2220 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2221 basis 4486=((prefixState SixCarryPrefixData.program 2217 basis 4486) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2220 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4486
 rw [gate_2220] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_2220 basis,frame_4486_2217_2220 basis] at h
 exact h

theorem gate_2221 : SixCarryPrefixData.program[2221]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4621 4486 4487 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 45 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[45]?=some (.CCX 4621 4486 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[2221]?=some (.CCX 4621 4486 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2221 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2222 basis 4487=((prefixState SixCarryPrefixData.program 969 basis 4487) ^^ ((prefixState SixCarryPrefixData.program 2220 basis 4621) && (prefixState SixCarryPrefixData.program 2221 basis 4486))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2221 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_2221] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4487_969_2221 basis,frame_4621_2220_2221 basis] at h
 exact h

theorem gate_2222 : SixCarryPrefixData.program[2222]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4357 4487 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 46 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[46]?=some (.CX 4357 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[2222]?=some (.CX 4357 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2222 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2223 basis 4487=((prefixState SixCarryPrefixData.program 2222 basis 4487) ^^ (prefixState SixCarryPrefixData.program 0 basis 4357)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2222 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_2222] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4357_0_2222 basis] at h
 exact h

theorem gate_2225 : SixCarryPrefixData.program[2225]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4622 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 49 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[49]?=some (.CX 4358 4622) := by decide +kernel
 have hh : SixCarryPrefixData.program[2225]?=some (.CX 4358 4622) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2225 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2226 basis 4622=((prefixState SixCarryPrefixData.program 1429 basis 4622) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2225 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4622
 rw [gate_2225] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_2225 basis,frame_4622_1429_2225 basis] at h
 exact h

theorem gate_2226 : SixCarryPrefixData.program[2226]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4487 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 50 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[50]?=some (.CX 4358 4487) := by decide +kernel
 have hh : SixCarryPrefixData.program[2226]?=some (.CX 4358 4487) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2226 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2227 basis 4487=((prefixState SixCarryPrefixData.program 2223 basis 4487) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2226 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4487
 rw [gate_2226] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_2226 basis,frame_4487_2223_2226 basis] at h
 exact h

theorem gate_2227 : SixCarryPrefixData.program[2227]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4622 4487 4488 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 51 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[51]?=some (.CCX 4622 4487 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[2227]?=some (.CCX 4622 4487 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2227 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2228 basis 4488=((prefixState SixCarryPrefixData.program 966 basis 4488) ^^ ((prefixState SixCarryPrefixData.program 2226 basis 4622) && (prefixState SixCarryPrefixData.program 2227 basis 4487))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2227 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_2227] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4488_966_2227 basis,frame_4622_2226_2227 basis] at h
 exact h

theorem gate_2228 : SixCarryPrefixData.program[2228]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4358 4488 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 52 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[52]?=some (.CX 4358 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[2228]?=some (.CX 4358 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2228 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2229 basis 4488=((prefixState SixCarryPrefixData.program 2228 basis 4488) ^^ (prefixState SixCarryPrefixData.program 0 basis 4358)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2228 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_2228] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4358_0_2228 basis] at h
 exact h

theorem gate_2231 : SixCarryPrefixData.program[2231]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4359 4623 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 55 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[55]?=some (.CX 4359 4623) := by decide +kernel
 have hh : SixCarryPrefixData.program[2231]?=some (.CX 4359 4623) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2231 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2232 basis 4623=((prefixState SixCarryPrefixData.program 1430 basis 4623) ^^ (prefixState SixCarryPrefixData.program 0 basis 4359)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2231 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4623
 rw [gate_2231] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4359_0_2231 basis,frame_4623_1430_2231 basis] at h
 exact h

theorem gate_2232 : SixCarryPrefixData.program[2232]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4359 4488 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 56 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[56]?=some (.CX 4359 4488) := by decide +kernel
 have hh : SixCarryPrefixData.program[2232]?=some (.CX 4359 4488) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2232 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2233 basis 4488=((prefixState SixCarryPrefixData.program 2229 basis 4488) ^^ (prefixState SixCarryPrefixData.program 0 basis 4359)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2232 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4488
 rw [gate_2232] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4359_0_2232 basis,frame_4488_2229_2232 basis] at h
 exact h

theorem gate_2233 : SixCarryPrefixData.program[2233]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4623 4488 4489 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 57 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[57]?=some (.CCX 4623 4488 4489) := by decide +kernel
 have hh : SixCarryPrefixData.program[2233]?=some (.CCX 4623 4488 4489) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2233 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2234 basis 4489=((prefixState SixCarryPrefixData.program 963 basis 4489) ^^ ((prefixState SixCarryPrefixData.program 2232 basis 4623) && (prefixState SixCarryPrefixData.program 2233 basis 4488))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2233 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4489
 rw [gate_2233] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4489_963_2233 basis,frame_4623_2232_2233 basis] at h
 exact h

theorem gate_2234 : SixCarryPrefixData.program[2234]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4359 4489 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 58 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[58]?=some (.CX 4359 4489) := by decide +kernel
 have hh : SixCarryPrefixData.program[2234]?=some (.CX 4359 4489) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2234 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2235 basis 4489=((prefixState SixCarryPrefixData.program 2234 basis 4489) ^^ (prefixState SixCarryPrefixData.program 0 basis 4359)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2234 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4489
 rw [gate_2234] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4359_0_2234 basis] at h
 exact h

theorem gate_2237 : SixCarryPrefixData.program[2237]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4360 4624 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 61 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[61]?=some (.CX 4360 4624) := by decide +kernel
 have hh : SixCarryPrefixData.program[2237]?=some (.CX 4360 4624) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2237 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2238 basis 4624=((prefixState SixCarryPrefixData.program 1431 basis 4624) ^^ (prefixState SixCarryPrefixData.program 0 basis 4360)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2237 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4624
 rw [gate_2237] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4360_0_2237 basis,frame_4624_1431_2237 basis] at h
 exact h

theorem gate_2238 : SixCarryPrefixData.program[2238]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4360 4489 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 62 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[62]?=some (.CX 4360 4489) := by decide +kernel
 have hh : SixCarryPrefixData.program[2238]?=some (.CX 4360 4489) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2238 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2239 basis 4489=((prefixState SixCarryPrefixData.program 2235 basis 4489) ^^ (prefixState SixCarryPrefixData.program 0 basis 4360)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2238 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4489
 rw [gate_2238] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4360_0_2238 basis,frame_4489_2235_2238 basis] at h
 exact h

theorem gate_2239 : SixCarryPrefixData.program[2239]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4624 4489 4490 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 63 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[63]?=some (.CCX 4624 4489 4490) := by decide +kernel
 have hh : SixCarryPrefixData.program[2239]?=some (.CCX 4624 4489 4490) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2239 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2240 basis 4490=((prefixState SixCarryPrefixData.program 960 basis 4490) ^^ ((prefixState SixCarryPrefixData.program 2238 basis 4624) && (prefixState SixCarryPrefixData.program 2239 basis 4489))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2239 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4490
 rw [gate_2239] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4490_960_2239 basis,frame_4624_2238_2239 basis] at h
 exact h

theorem gate_2240 : SixCarryPrefixData.program[2240]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4360 4490 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 64 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[64]?=some (.CX 4360 4490) := by decide +kernel
 have hh : SixCarryPrefixData.program[2240]?=some (.CX 4360 4490) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2240 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2241 basis 4490=((prefixState SixCarryPrefixData.program 2240 basis 4490) ^^ (prefixState SixCarryPrefixData.program 0 basis 4360)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2240 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4490
 rw [gate_2240] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4360_0_2240 basis] at h
 exact h

theorem gate_2243 : SixCarryPrefixData.program[2243]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4361 4625 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 67 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[67]?=some (.CX 4361 4625) := by decide +kernel
 have hh : SixCarryPrefixData.program[2243]?=some (.CX 4361 4625) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2243 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2244 basis 4625=((prefixState SixCarryPrefixData.program 1432 basis 4625) ^^ (prefixState SixCarryPrefixData.program 0 basis 4361)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2243 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4625
 rw [gate_2243] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4361_0_2243 basis,frame_4625_1432_2243 basis] at h
 exact h

theorem gate_2244 : SixCarryPrefixData.program[2244]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4361 4490 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 68 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[68]?=some (.CX 4361 4490) := by decide +kernel
 have hh : SixCarryPrefixData.program[2244]?=some (.CX 4361 4490) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2244 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2245 basis 4490=((prefixState SixCarryPrefixData.program 2241 basis 4490) ^^ (prefixState SixCarryPrefixData.program 0 basis 4361)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2244 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4490
 rw [gate_2244] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4361_0_2244 basis,frame_4490_2241_2244 basis] at h
 exact h

theorem gate_2245 : SixCarryPrefixData.program[2245]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4625 4490 4491 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 69 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[69]?=some (.CCX 4625 4490 4491) := by decide +kernel
 have hh : SixCarryPrefixData.program[2245]?=some (.CCX 4625 4490 4491) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2245 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2246 basis 4491=((prefixState SixCarryPrefixData.program 957 basis 4491) ^^ ((prefixState SixCarryPrefixData.program 2244 basis 4625) && (prefixState SixCarryPrefixData.program 2245 basis 4490))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2245 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4491
 rw [gate_2245] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4491_957_2245 basis,frame_4625_2244_2245 basis] at h
 exact h

theorem gate_2246 : SixCarryPrefixData.program[2246]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4361 4491 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 70 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[70]?=some (.CX 4361 4491) := by decide +kernel
 have hh : SixCarryPrefixData.program[2246]?=some (.CX 4361 4491) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2246 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2247 basis 4491=((prefixState SixCarryPrefixData.program 2246 basis 4491) ^^ (prefixState SixCarryPrefixData.program 0 basis 4361)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2246 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4491
 rw [gate_2246] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4361_0_2246 basis] at h
 exact h

theorem gate_2249 : SixCarryPrefixData.program[2249]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4362 4626 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 73 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[73]?=some (.CX 4362 4626) := by decide +kernel
 have hh : SixCarryPrefixData.program[2249]?=some (.CX 4362 4626) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2249 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2250 basis 4626=((prefixState SixCarryPrefixData.program 1433 basis 4626) ^^ (prefixState SixCarryPrefixData.program 0 basis 4362)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2249 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4626
 rw [gate_2249] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4362_0_2249 basis,frame_4626_1433_2249 basis] at h
 exact h

theorem gate_2250 : SixCarryPrefixData.program[2250]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4362 4491 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 74 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[74]?=some (.CX 4362 4491) := by decide +kernel
 have hh : SixCarryPrefixData.program[2250]?=some (.CX 4362 4491) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2250 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2251 basis 4491=((prefixState SixCarryPrefixData.program 2247 basis 4491) ^^ (prefixState SixCarryPrefixData.program 0 basis 4362)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2250 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4491
 rw [gate_2250] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4362_0_2250 basis,frame_4491_2247_2250 basis] at h
 exact h

theorem gate_2251 : SixCarryPrefixData.program[2251]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CCX 4626 4491 4492 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 75 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[75]?=some (.CCX 4626 4491 4492) := by decide +kernel
 have hh : SixCarryPrefixData.program[2251]?=some (.CCX 4626 4491 4492) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2251 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2252 basis 4492=((prefixState SixCarryPrefixData.program 954 basis 4492) ^^ ((prefixState SixCarryPrefixData.program 2250 basis 4626) && (prefixState SixCarryPrefixData.program 2251 basis 4491))) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2251 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4492
 rw [gate_2251] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4492_954_2251 basis,frame_4626_2250_2251 basis] at h
 exact h

theorem gate_2252 : SixCarryPrefixData.program[2252]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4362 4492 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 76 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[76]?=some (.CX 4362 4492) := by decide +kernel
 have hh : SixCarryPrefixData.program[2252]?=some (.CX 4362 4492) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2252 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2253 basis 4492=((prefixState SixCarryPrefixData.program 2252 basis 4492) ^^ (prefixState SixCarryPrefixData.program 0 basis 4362)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2252 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4492
 rw [gate_2252] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4362_0_2252 basis] at h
 exact h

theorem gate_2256 : SixCarryPrefixData.program[2256]'(by rw [SixCarryPrefixData.program_length]; decide +kernel)=.CX 4363 4492 := by
 have h := lookup_context SixCarryPrefixData.program before17 SixCarryPrefixData.chunk17 after17 2176 80 shape17 before_len17 (by rw [len17]; decide +kernel)
 have hg : SixCarryPrefixData.chunk17[80]?=some (.CX 4363 4492) := by decide +kernel
 have hh : SixCarryPrefixData.program[2256]?=some (.CX 4363 4492) := h.trans hg
 exact (List.getElem?_eq_some_iff.mp hh).2

theorem step_2256 (basis : BasisState) :
 prefixState SixCarryPrefixData.program 2257 basis 4492=((prefixState SixCarryPrefixData.program 2253 basis 4492) ^^ (prefixState SixCarryPrefixData.program 0 basis 4363)) := by
 have h := congrFun (at_succ SixCarryPrefixData.program 2256 (by rw [SixCarryPrefixData.program_length]; decide +kernel) basis) 4492
 rw [gate_2256] at h
 simp only [basisStep,writeBit,Function.update_self] at h
 rw [frame_4363_0_2256 basis,frame_4492_2253_2256 basis] at h
 exact h

end ECDSAAdd.Entrant.ExtraCarryTrace4907
