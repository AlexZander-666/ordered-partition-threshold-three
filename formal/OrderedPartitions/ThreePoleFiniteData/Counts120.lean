import OrderedPartitions.ThreePoleFiniteData.Arithmetic120
import OrderedPartitions.ThreePoleFiniteData.Counts112

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory120 : HistoryOK 120 history120 :=
  historyPush checkedHistory119 checkedWeights120 checkedRow120
theorem original120 : poly coeffs120 = row 120 3 :=
  head_original (checkedHistory120)

theorem checkedHistory121 : HistoryOK 121 history121 :=
  historyPush checkedHistory120 checkedWeights121 checkedRow121
theorem original121 : poly coeffs121 = row 121 3 :=
  head_original (checkedHistory121)

theorem checkedHistory122 : HistoryOK 122 history122 :=
  historyPush checkedHistory121 checkedWeights122 checkedRow122
theorem original122 : poly coeffs122 = row 122 3 :=
  head_original (checkedHistory122)

theorem checkedHistory123 : HistoryOK 123 history123 :=
  historyPush checkedHistory122 checkedWeights123 checkedRow123
theorem original123 : poly coeffs123 = row 123 3 :=
  head_original (checkedHistory123)

theorem checkedHistory124 : HistoryOK 124 history124 :=
  historyPush checkedHistory123 checkedWeights124 checkedRow124
theorem original124 : poly coeffs124 = row 124 3 :=
  head_original (checkedHistory124)

theorem checkedHistory125 : HistoryOK 125 history125 :=
  historyPush checkedHistory124 checkedWeights125 checkedRow125
theorem original125 : poly coeffs125 = row 125 3 :=
  head_original (checkedHistory125)

theorem checkedHistory126 : HistoryOK 126 history126 :=
  historyPush checkedHistory125 checkedWeights126 checkedRow126
theorem original126 : poly coeffs126 = row 126 3 :=
  head_original (checkedHistory126)

theorem checkedHistory127 : HistoryOK 127 history127 :=
  historyPush checkedHistory126 checkedWeights127 checkedRow127
theorem original127 : poly coeffs127 = row 127 3 :=
  head_original (checkedHistory127)


#print axioms original127

end OrderedPartitions.ThreePoleFinite
