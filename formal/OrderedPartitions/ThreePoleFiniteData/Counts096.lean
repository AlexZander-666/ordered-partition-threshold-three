import OrderedPartitions.ThreePoleFiniteData.Arithmetic096
import OrderedPartitions.ThreePoleFiniteData.Counts088

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory96 : HistoryOK 96 history96 :=
  historyPush checkedHistory95 checkedWeights96 checkedRow96
theorem original96 : poly coeffs96 = row 96 3 :=
  head_original (checkedHistory96)

theorem checkedHistory97 : HistoryOK 97 history97 :=
  historyPush checkedHistory96 checkedWeights97 checkedRow97
theorem original97 : poly coeffs97 = row 97 3 :=
  head_original (checkedHistory97)

theorem checkedHistory98 : HistoryOK 98 history98 :=
  historyPush checkedHistory97 checkedWeights98 checkedRow98
theorem original98 : poly coeffs98 = row 98 3 :=
  head_original (checkedHistory98)

theorem checkedHistory99 : HistoryOK 99 history99 :=
  historyPush checkedHistory98 checkedWeights99 checkedRow99
theorem original99 : poly coeffs99 = row 99 3 :=
  head_original (checkedHistory99)

theorem checkedHistory100 : HistoryOK 100 history100 :=
  historyPush checkedHistory99 checkedWeights100 checkedRow100
theorem original100 : poly coeffs100 = row 100 3 :=
  head_original (checkedHistory100)

theorem checkedHistory101 : HistoryOK 101 history101 :=
  historyPush checkedHistory100 checkedWeights101 checkedRow101
theorem original101 : poly coeffs101 = row 101 3 :=
  head_original (checkedHistory101)

theorem checkedHistory102 : HistoryOK 102 history102 :=
  historyPush checkedHistory101 checkedWeights102 checkedRow102
theorem original102 : poly coeffs102 = row 102 3 :=
  head_original (checkedHistory102)

theorem checkedHistory103 : HistoryOK 103 history103 :=
  historyPush checkedHistory102 checkedWeights103 checkedRow103
theorem original103 : poly coeffs103 = row 103 3 :=
  head_original (checkedHistory103)


#print axioms original103

end OrderedPartitions.ThreePoleFinite
