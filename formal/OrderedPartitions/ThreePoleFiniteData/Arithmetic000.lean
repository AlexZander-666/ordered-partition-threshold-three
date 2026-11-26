import OrderedPartitions.ThreePoleFiniteData.Raw000
import OrderedPartitions.ThreePoleFiniteVector

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def weights1 : Weights := [
  (1,1)
]
theorem checkedWeights1 : weights1 = weights 1 := by decide +kernel
private theorem vectorOK1 : vectorOK 1 history0 weights1 coeffs1 = true := by
  decide +kernel
theorem checkedRow1 : rowOK 1 history0 weights1 coeffs1 = true :=
  vector_sound vectorOK1

def weights2 : Weights := [
  (1,2), (2,1)
]
theorem checkedWeights2 : weights2 = weights 2 := by decide +kernel
private theorem vectorOK2 : vectorOK 2 history1 weights2 coeffs2 = true := by
  decide +kernel
theorem checkedRow2 : rowOK 2 history1 weights2 coeffs2 = true :=
  vector_sound vectorOK2

def weights3 : Weights := [
  (1,3), (2,3),
  (3,1)
]
theorem checkedWeights3 : weights3 = weights 3 := by decide +kernel
private theorem vectorOK3 : vectorOK 3 history2 weights3 coeffs3 = true := by
  decide +kernel
theorem checkedRow3 : rowOK 3 history2 weights3 coeffs3 = true :=
  vector_sound vectorOK3

def weights4 : Weights := [
  (1,4), (2,6),
  (3,4), (4,1)
]
theorem checkedWeights4 : weights4 = weights 4 := by decide +kernel
private theorem vectorOK4 : vectorOK 4 history3 weights4 coeffs4 = true := by
  decide +kernel
theorem checkedRow4 : rowOK 4 history3 weights4 coeffs4 = true :=
  vector_sound vectorOK4

def weights5 : Weights := [
  (1,5), (2,10),
  (3,10), (4,5),
  (5,1)
]
theorem checkedWeights5 : weights5 = weights 5 := by decide +kernel
private theorem vectorOK5 : vectorOK 5 history4 weights5 coeffs5 = true := by
  decide +kernel
theorem checkedRow5 : rowOK 5 history4 weights5 coeffs5 = true :=
  vector_sound vectorOK5

def weights6 : Weights := [
  (1,6), (2,15),
  (3,20), (4,15),
  (5,6), (6,1)
]
theorem checkedWeights6 : weights6 = weights 6 := by decide +kernel
private theorem vectorOK6 : vectorOK 6 history5 weights6 coeffs6 = true := by
  decide +kernel
theorem checkedRow6 : rowOK 6 history5 weights6 coeffs6 = true :=
  vector_sound vectorOK6

def weights7 : Weights := [
  (1,7), (2,21),
  (3,35), (4,35),
  (5,21), (6,7),
  (7,1)
]
theorem checkedWeights7 : weights7 = weights 7 := by decide +kernel
private theorem vectorOK7 : vectorOK 7 history6 weights7 coeffs7 = true := by
  decide +kernel
theorem checkedRow7 : rowOK 7 history6 weights7 coeffs7 = true :=
  vector_sound vectorOK7


#print axioms checkedRow7

end OrderedPartitions.ThreePoleFinite
