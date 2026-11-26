import OrderedPartitions.ThreePoleFiniteData.Raw008
import OrderedPartitions.ThreePoleFiniteVector

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def weights8 : Weights := [
  (1,8), (2,28),
  (3,56), (4,70),
  (5,56), (6,28),
  (7,8), (8,1)
]
theorem checkedWeights8 : weights8 = weights 8 := by decide +kernel
private theorem vectorOK8 : vectorOK 8 history7 weights8 coeffs8 = true := by
  decide +kernel
theorem checkedRow8 : rowOK 8 history7 weights8 coeffs8 = true :=
  vector_sound vectorOK8

def weights9 : Weights := [
  (1,9), (2,36),
  (3,84), (4,126),
  (5,126), (6,84),
  (7,36), (8,9),
  (9,1)
]
theorem checkedWeights9 : weights9 = weights 9 := by decide +kernel
private theorem vectorOK9 : vectorOK 9 history8 weights9 coeffs9 = true := by
  decide +kernel
theorem checkedRow9 : rowOK 9 history8 weights9 coeffs9 = true :=
  vector_sound vectorOK9

def weights10 : Weights := [
  (1,10), (2,45),
  (3,120), (4,210),
  (5,252), (6,210),
  (7,120), (8,45),
  (9,10), (10,1)
]
theorem checkedWeights10 : weights10 = weights 10 := by decide +kernel
private theorem vectorOK10 : vectorOK 10 history9 weights10 coeffs10 = true := by
  decide +kernel
theorem checkedRow10 : rowOK 10 history9 weights10 coeffs10 = true :=
  vector_sound vectorOK10

def weights11 : Weights := [
  (1,11), (2,55),
  (3,165), (4,330),
  (5,462), (6,462),
  (7,330), (8,165),
  (9,55), (10,11),
  (11,1)
]
theorem checkedWeights11 : weights11 = weights 11 := by decide +kernel
private theorem vectorOK11 : vectorOK 11 history10 weights11 coeffs11 = true := by
  decide +kernel
theorem checkedRow11 : rowOK 11 history10 weights11 coeffs11 = true :=
  vector_sound vectorOK11

def weights12 : Weights := [
  (1,12), (2,66),
  (3,220), (4,495),
  (5,792), (6,924),
  (7,792), (8,495),
  (9,220), (10,66),
  (11,12), (12,1)
]
theorem checkedWeights12 : weights12 = weights 12 := by decide +kernel
private theorem vectorOK12 : vectorOK 12 history11 weights12 coeffs12 = true := by
  decide +kernel
theorem checkedRow12 : rowOK 12 history11 weights12 coeffs12 = true :=
  vector_sound vectorOK12

def weights13 : Weights := [
  (1,13), (2,78),
  (3,286), (4,715),
  (5,1287), (6,1716),
  (7,1716), (8,1287),
  (9,715), (10,286),
  (11,78), (12,13),
  (13,1)
]
theorem checkedWeights13 : weights13 = weights 13 := by decide +kernel
private theorem vectorOK13 : vectorOK 13 history12 weights13 coeffs13 = true := by
  decide +kernel
theorem checkedRow13 : rowOK 13 history12 weights13 coeffs13 = true :=
  vector_sound vectorOK13

def weights14 : Weights := [
  (1,14), (2,91),
  (3,364), (4,1001),
  (5,2002), (6,3003),
  (7,3432), (8,3003),
  (9,2002), (10,1001),
  (11,364), (12,91),
  (13,14), (14,1)
]
theorem checkedWeights14 : weights14 = weights 14 := by decide +kernel
private theorem vectorOK14 : vectorOK 14 history13 weights14 coeffs14 = true := by
  decide +kernel
theorem checkedRow14 : rowOK 14 history13 weights14 coeffs14 = true :=
  vector_sound vectorOK14

def weights15 : Weights := [
  (1,15), (2,105),
  (3,455), (4,1365),
  (5,3003), (6,5005),
  (7,6435), (8,6435),
  (9,5005), (10,3003),
  (11,1365), (12,455),
  (13,105), (14,15),
  (15,1)
]
theorem checkedWeights15 : weights15 = weights 15 := by decide +kernel
private theorem vectorOK15 : vectorOK 15 history14 weights15 coeffs15 = true := by
  decide +kernel
theorem checkedRow15 : rowOK 15 history14 weights15 coeffs15 = true :=
  vector_sound vectorOK15


#print axioms checkedRow15

end OrderedPartitions.ThreePoleFinite
