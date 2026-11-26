import OrderedPartitions.ThreePoleFiniteData.Raw024
import OrderedPartitions.ThreePoleFiniteVector

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def weights24 : Weights := [
  (1,24), (2,276),
  (3,2024), (4,10626),
  (5,42504), (6,134596),
  (7,346104), (8,735471),
  (9,1307504), (10,1961256),
  (11,2496144), (12,2704156),
  (13,2496144), (14,1961256),
  (15,1307504), (16,735471),
  (17,346104), (18,134596),
  (19,42504), (20,10626),
  (21,2024), (22,276),
  (23,24), (24,1)
]
theorem checkedWeights24 : weights24 = weights 24 := by decide +kernel
private theorem vectorOK24 : vectorOK 24 history23 weights24 coeffs24 = true := by
  decide +kernel
theorem checkedRow24 : rowOK 24 history23 weights24 coeffs24 = true :=
  vector_sound vectorOK24

def weights25 : Weights := [
  (1,25), (2,300),
  (3,2300), (4,12650),
  (5,53130), (6,177100),
  (7,480700), (8,1081575),
  (9,2042975), (10,3268760),
  (11,4457400), (12,5200300),
  (13,5200300), (14,4457400),
  (15,3268760), (16,2042975),
  (17,1081575), (18,480700),
  (19,177100), (20,53130),
  (21,12650), (22,2300),
  (23,300), (24,25),
  (25,1)
]
theorem checkedWeights25 : weights25 = weights 25 := by decide +kernel
private theorem vectorOK25 : vectorOK 25 history24 weights25 coeffs25 = true := by
  decide +kernel
theorem checkedRow25 : rowOK 25 history24 weights25 coeffs25 = true :=
  vector_sound vectorOK25

def weights26 : Weights := [
  (1,26), (2,325),
  (3,2600), (4,14950),
  (5,65780), (6,230230),
  (7,657800), (8,1562275),
  (9,3124550), (10,5311735),
  (11,7726160), (12,9657700),
  (13,10400600), (14,9657700),
  (15,7726160), (16,5311735),
  (17,3124550), (18,1562275),
  (19,657800), (20,230230),
  (21,65780), (22,14950),
  (23,2600), (24,325),
  (25,26), (26,1)
]
theorem checkedWeights26 : weights26 = weights 26 := by decide +kernel
private theorem vectorOK26 : vectorOK 26 history25 weights26 coeffs26 = true := by
  decide +kernel
theorem checkedRow26 : rowOK 26 history25 weights26 coeffs26 = true :=
  vector_sound vectorOK26

def weights27 : Weights := [
  (1,27), (2,351),
  (3,2925), (4,17550),
  (5,80730), (6,296010),
  (7,888030), (8,2220075),
  (9,4686825), (10,8436285),
  (11,13037895), (12,17383860),
  (13,20058300), (14,20058300),
  (15,17383860), (16,13037895),
  (17,8436285), (18,4686825),
  (19,2220075), (20,888030),
  (21,296010), (22,80730),
  (23,17550), (24,2925),
  (25,351), (26,27),
  (27,1)
]
theorem checkedWeights27 : weights27 = weights 27 := by decide +kernel
private theorem vectorOK27 : vectorOK 27 history26 weights27 coeffs27 = true := by
  decide +kernel
theorem checkedRow27 : rowOK 27 history26 weights27 coeffs27 = true :=
  vector_sound vectorOK27

def weights28 : Weights := [
  (1,28), (2,378),
  (3,3276), (4,20475),
  (5,98280), (6,376740),
  (7,1184040), (8,3108105),
  (9,6906900), (10,13123110),
  (11,21474180), (12,30421755),
  (13,37442160), (14,40116600),
  (15,37442160), (16,30421755),
  (17,21474180), (18,13123110),
  (19,6906900), (20,3108105),
  (21,1184040), (22,376740),
  (23,98280), (24,20475),
  (25,3276), (26,378),
  (27,28), (28,1)
]
theorem checkedWeights28 : weights28 = weights 28 := by decide +kernel
private theorem vectorOK28 : vectorOK 28 history27 weights28 coeffs28 = true := by
  decide +kernel
theorem checkedRow28 : rowOK 28 history27 weights28 coeffs28 = true :=
  vector_sound vectorOK28

def weights29 : Weights := [
  (1,29), (2,406),
  (3,3654), (4,23751),
  (5,118755), (6,475020),
  (7,1560780), (8,4292145),
  (9,10015005), (10,20030010),
  (11,34597290), (12,51895935),
  (13,67863915), (14,77558760),
  (15,77558760), (16,67863915),
  (17,51895935), (18,34597290),
  (19,20030010), (20,10015005),
  (21,4292145), (22,1560780),
  (23,475020), (24,118755),
  (25,23751), (26,3654),
  (27,406), (28,29),
  (29,1)
]
theorem checkedWeights29 : weights29 = weights 29 := by decide +kernel
private theorem vectorOK29 : vectorOK 29 history28 weights29 coeffs29 = true := by
  decide +kernel
theorem checkedRow29 : rowOK 29 history28 weights29 coeffs29 = true :=
  vector_sound vectorOK29

def weights30 : Weights := [
  (1,30), (2,435),
  (3,4060), (4,27405),
  (5,142506), (6,593775),
  (7,2035800), (8,5852925),
  (9,14307150), (10,30045015),
  (11,54627300), (12,86493225),
  (13,119759850), (14,145422675),
  (15,155117520), (16,145422675),
  (17,119759850), (18,86493225),
  (19,54627300), (20,30045015),
  (21,14307150), (22,5852925),
  (23,2035800), (24,593775),
  (25,142506), (26,27405),
  (27,4060), (28,435),
  (29,30), (30,1)
]
theorem checkedWeights30 : weights30 = weights 30 := by decide +kernel
private theorem vectorOK30 : vectorOK 30 history29 weights30 coeffs30 = true := by
  decide +kernel
theorem checkedRow30 : rowOK 30 history29 weights30 coeffs30 = true :=
  vector_sound vectorOK30

def weights31 : Weights := [
  (1,31), (2,465),
  (3,4495), (4,31465),
  (5,169911), (6,736281),
  (7,2629575), (8,7888725),
  (9,20160075), (10,44352165),
  (11,84672315), (12,141120525),
  (13,206253075), (14,265182525),
  (15,300540195), (16,300540195),
  (17,265182525), (18,206253075),
  (19,141120525), (20,84672315),
  (21,44352165), (22,20160075),
  (23,7888725), (24,2629575),
  (25,736281), (26,169911),
  (27,31465), (28,4495),
  (29,465), (30,31),
  (31,1)
]
theorem checkedWeights31 : weights31 = weights 31 := by decide +kernel
private theorem vectorOK31 : vectorOK 31 history30 weights31 coeffs31 = true := by
  decide +kernel
theorem checkedRow31 : rowOK 31 history30 weights31 coeffs31 = true :=
  vector_sound vectorOK31


#print axioms checkedRow31

end OrderedPartitions.ThreePoleFinite
