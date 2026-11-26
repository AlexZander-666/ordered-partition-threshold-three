import OrderedPartitions.ThreePoleFiniteData.Arithmetic088
import OrderedPartitions.ThreePoleFiniteData.Counts080

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory88 : HistoryOK 88 history88 :=
  historyPush checkedHistory87 checkedWeights88 checkedRow88
theorem original88 : poly coeffs88 = row 88 3 :=
  head_original (checkedHistory88)

theorem checkedHistory89 : HistoryOK 89 history89 :=
  historyPush checkedHistory88 checkedWeights89 checkedRow89
theorem original89 : poly coeffs89 = row 89 3 :=
  head_original (checkedHistory89)

theorem checkedHistory90 : HistoryOK 90 history90 :=
  historyPush checkedHistory89 checkedWeights90 checkedRow90
theorem original90 : poly coeffs90 = row 90 3 :=
  head_original (checkedHistory90)

theorem checkedHistory91 : HistoryOK 91 history91 :=
  historyPush checkedHistory90 checkedWeights91 checkedRow91
theorem original91 : poly coeffs91 = row 91 3 :=
  head_original (checkedHistory91)

theorem checkedHistory92 : HistoryOK 92 history92 :=
  historyPush checkedHistory91 checkedWeights92 checkedRow92
theorem original92 : poly coeffs92 = row 92 3 :=
  head_original (checkedHistory92)

theorem checkedHistory93 : HistoryOK 93 history93 :=
  historyPush checkedHistory92 checkedWeights93 checkedRow93
theorem original93 : poly coeffs93 = row 93 3 :=
  head_original (checkedHistory93)

theorem checkedHistory94 : HistoryOK 94 history94 :=
  historyPush checkedHistory93 checkedWeights94 checkedRow94
theorem original94 : poly coeffs94 = row 94 3 :=
  head_original (checkedHistory94)

theorem checkedHistory95 : HistoryOK 95 history95 :=
  historyPush checkedHistory94 checkedWeights95 checkedRow95
theorem original95 : poly coeffs95 = row 95 3 :=
  head_original (checkedHistory95)


#print axioms original95

end OrderedPartitions.ThreePoleFinite
