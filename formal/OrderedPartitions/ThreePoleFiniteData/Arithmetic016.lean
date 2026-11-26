import OrderedPartitions.ThreePoleFiniteData.Raw016
import OrderedPartitions.ThreePoleFiniteVector

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def weights16 : Weights := [
  (1,16), (2,120),
  (3,560), (4,1820),
  (5,4368), (6,8008),
  (7,11440), (8,12870),
  (9,11440), (10,8008),
  (11,4368), (12,1820),
  (13,560), (14,120),
  (15,16), (16,1)
]
theorem checkedWeights16 : weights16 = weights 16 := by decide +kernel
private theorem vectorOK16 : vectorOK 16 history15 weights16 coeffs16 = true := by
  decide +kernel
theorem checkedRow16 : rowOK 16 history15 weights16 coeffs16 = true :=
  vector_sound vectorOK16

def weights17 : Weights := [
  (1,17), (2,136),
  (3,680), (4,2380),
  (5,6188), (6,12376),
  (7,19448), (8,24310),
  (9,24310), (10,19448),
  (11,12376), (12,6188),
  (13,2380), (14,680),
  (15,136), (16,17),
  (17,1)
]
theorem checkedWeights17 : weights17 = weights 17 := by decide +kernel
private theorem vectorOK17 : vectorOK 17 history16 weights17 coeffs17 = true := by
  decide +kernel
theorem checkedRow17 : rowOK 17 history16 weights17 coeffs17 = true :=
  vector_sound vectorOK17

def weights18 : Weights := [
  (1,18), (2,153),
  (3,816), (4,3060),
  (5,8568), (6,18564),
  (7,31824), (8,43758),
  (9,48620), (10,43758),
  (11,31824), (12,18564),
  (13,8568), (14,3060),
  (15,816), (16,153),
  (17,18), (18,1)
]
theorem checkedWeights18 : weights18 = weights 18 := by decide +kernel
private theorem vectorOK18 : vectorOK 18 history17 weights18 coeffs18 = true := by
  decide +kernel
theorem checkedRow18 : rowOK 18 history17 weights18 coeffs18 = true :=
  vector_sound vectorOK18

def weights19 : Weights := [
  (1,19), (2,171),
  (3,969), (4,3876),
  (5,11628), (6,27132),
  (7,50388), (8,75582),
  (9,92378), (10,92378),
  (11,75582), (12,50388),
  (13,27132), (14,11628),
  (15,3876), (16,969),
  (17,171), (18,19),
  (19,1)
]
theorem checkedWeights19 : weights19 = weights 19 := by decide +kernel
private theorem vectorOK19 : vectorOK 19 history18 weights19 coeffs19 = true := by
  decide +kernel
theorem checkedRow19 : rowOK 19 history18 weights19 coeffs19 = true :=
  vector_sound vectorOK19

def weights20 : Weights := [
  (1,20), (2,190),
  (3,1140), (4,4845),
  (5,15504), (6,38760),
  (7,77520), (8,125970),
  (9,167960), (10,184756),
  (11,167960), (12,125970),
  (13,77520), (14,38760),
  (15,15504), (16,4845),
  (17,1140), (18,190),
  (19,20), (20,1)
]
theorem checkedWeights20 : weights20 = weights 20 := by decide +kernel
private theorem vectorOK20 : vectorOK 20 history19 weights20 coeffs20 = true := by
  decide +kernel
theorem checkedRow20 : rowOK 20 history19 weights20 coeffs20 = true :=
  vector_sound vectorOK20

def weights21 : Weights := [
  (1,21), (2,210),
  (3,1330), (4,5985),
  (5,20349), (6,54264),
  (7,116280), (8,203490),
  (9,293930), (10,352716),
  (11,352716), (12,293930),
  (13,203490), (14,116280),
  (15,54264), (16,20349),
  (17,5985), (18,1330),
  (19,210), (20,21),
  (21,1)
]
theorem checkedWeights21 : weights21 = weights 21 := by decide +kernel
private theorem vectorOK21 : vectorOK 21 history20 weights21 coeffs21 = true := by
  decide +kernel
theorem checkedRow21 : rowOK 21 history20 weights21 coeffs21 = true :=
  vector_sound vectorOK21

def weights22 : Weights := [
  (1,22), (2,231),
  (3,1540), (4,7315),
  (5,26334), (6,74613),
  (7,170544), (8,319770),
  (9,497420), (10,646646),
  (11,705432), (12,646646),
  (13,497420), (14,319770),
  (15,170544), (16,74613),
  (17,26334), (18,7315),
  (19,1540), (20,231),
  (21,22), (22,1)
]
theorem checkedWeights22 : weights22 = weights 22 := by decide +kernel
private theorem vectorOK22 : vectorOK 22 history21 weights22 coeffs22 = true := by
  decide +kernel
theorem checkedRow22 : rowOK 22 history21 weights22 coeffs22 = true :=
  vector_sound vectorOK22

def weights23 : Weights := [
  (1,23), (2,253),
  (3,1771), (4,8855),
  (5,33649), (6,100947),
  (7,245157), (8,490314),
  (9,817190), (10,1144066),
  (11,1352078), (12,1352078),
  (13,1144066), (14,817190),
  (15,490314), (16,245157),
  (17,100947), (18,33649),
  (19,8855), (20,1771),
  (21,253), (22,23),
  (23,1)
]
theorem checkedWeights23 : weights23 = weights 23 := by decide +kernel
private theorem vectorOK23 : vectorOK 23 history22 weights23 coeffs23 = true := by
  decide +kernel
theorem checkedRow23 : rowOK 23 history22 weights23 coeffs23 = true :=
  vector_sound vectorOK23


#print axioms checkedRow23

end OrderedPartitions.ThreePoleFinite
