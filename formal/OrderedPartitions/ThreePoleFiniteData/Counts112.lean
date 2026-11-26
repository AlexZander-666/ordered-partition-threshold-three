import OrderedPartitions.ThreePoleFiniteData.Arithmetic112
import OrderedPartitions.ThreePoleFiniteData.Counts104

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory112 : HistoryOK 112 history112 :=
  historyPush checkedHistory111 checkedWeights112 checkedRow112
theorem original112 : poly coeffs112 = row 112 3 :=
  head_original (checkedHistory112)

theorem checkedHistory113 : HistoryOK 113 history113 :=
  historyPush checkedHistory112 checkedWeights113 checkedRow113
theorem original113 : poly coeffs113 = row 113 3 :=
  head_original (checkedHistory113)

theorem checkedHistory114 : HistoryOK 114 history114 :=
  historyPush checkedHistory113 checkedWeights114 checkedRow114
theorem original114 : poly coeffs114 = row 114 3 :=
  head_original (checkedHistory114)

theorem checkedHistory115 : HistoryOK 115 history115 :=
  historyPush checkedHistory114 checkedWeights115 checkedRow115
theorem original115 : poly coeffs115 = row 115 3 :=
  head_original (checkedHistory115)

theorem checkedHistory116 : HistoryOK 116 history116 :=
  historyPush checkedHistory115 checkedWeights116 checkedRow116
theorem original116 : poly coeffs116 = row 116 3 :=
  head_original (checkedHistory116)

theorem checkedHistory117 : HistoryOK 117 history117 :=
  historyPush checkedHistory116 checkedWeights117 checkedRow117
theorem original117 : poly coeffs117 = row 117 3 :=
  head_original (checkedHistory117)

theorem checkedHistory118 : HistoryOK 118 history118 :=
  historyPush checkedHistory117 checkedWeights118 checkedRow118
theorem original118 : poly coeffs118 = row 118 3 :=
  head_original (checkedHistory118)

theorem checkedHistory119 : HistoryOK 119 history119 :=
  historyPush checkedHistory118 checkedWeights119 checkedRow119
theorem original119 : poly coeffs119 = row 119 3 :=
  head_original (checkedHistory119)


#print axioms original119

end OrderedPartitions.ThreePoleFinite
