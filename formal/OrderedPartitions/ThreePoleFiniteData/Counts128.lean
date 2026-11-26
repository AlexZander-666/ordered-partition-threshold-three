import OrderedPartitions.ThreePoleFiniteData.Arithmetic128
import OrderedPartitions.ThreePoleFiniteData.Counts120

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory128 : HistoryOK 128 history128 :=
  historyPush checkedHistory127 checkedWeights128 checkedRow128
theorem original128 : poly coeffs128 = row 128 3 :=
  head_original (checkedHistory128)

theorem checkedHistory129 : HistoryOK 129 history129 :=
  historyPush checkedHistory128 checkedWeights129 checkedRow129
theorem original129 : poly coeffs129 = row 129 3 :=
  head_original (checkedHistory129)

theorem checkedHistory130 : HistoryOK 130 history130 :=
  historyPush checkedHistory129 checkedWeights130 checkedRow130
theorem original130 : poly coeffs130 = row 130 3 :=
  head_original (checkedHistory130)

theorem checkedHistory131 : HistoryOK 131 history131 :=
  historyPush checkedHistory130 checkedWeights131 checkedRow131
theorem original131 : poly coeffs131 = row 131 3 :=
  head_original (checkedHistory131)

theorem checkedHistory132 : HistoryOK 132 history132 :=
  historyPush checkedHistory131 checkedWeights132 checkedRow132
theorem original132 : poly coeffs132 = row 132 3 :=
  head_original (checkedHistory132)

theorem checkedHistory133 : HistoryOK 133 history133 :=
  historyPush checkedHistory132 checkedWeights133 checkedRow133
theorem original133 : poly coeffs133 = row 133 3 :=
  head_original (checkedHistory133)

theorem checkedHistory134 : HistoryOK 134 history134 :=
  historyPush checkedHistory133 checkedWeights134 checkedRow134
theorem original134 : poly coeffs134 = row 134 3 :=
  head_original (checkedHistory134)

theorem checkedHistory135 : HistoryOK 135 history135 :=
  historyPush checkedHistory134 checkedWeights135 checkedRow135
theorem original135 : poly coeffs135 = row 135 3 :=
  head_original (checkedHistory135)


#print axioms original135

end OrderedPartitions.ThreePoleFinite
