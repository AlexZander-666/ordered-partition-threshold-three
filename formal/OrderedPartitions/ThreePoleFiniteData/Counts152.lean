import OrderedPartitions.ThreePoleFiniteData.Arithmetic152
import OrderedPartitions.ThreePoleFiniteData.Counts144

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory152 : HistoryOK 152 history152 :=
  historyPush checkedHistory151 checkedWeights152 checkedRow152
theorem original152 : poly coeffs152 = row 152 3 :=
  head_original (checkedHistory152)

theorem checkedHistory153 : HistoryOK 153 history153 :=
  historyPush checkedHistory152 checkedWeights153 checkedRow153
theorem original153 : poly coeffs153 = row 153 3 :=
  head_original (checkedHistory153)

theorem checkedHistory154 : HistoryOK 154 history154 :=
  historyPush checkedHistory153 checkedWeights154 checkedRow154
theorem original154 : poly coeffs154 = row 154 3 :=
  head_original (checkedHistory154)

theorem checkedHistory155 : HistoryOK 155 history155 :=
  historyPush checkedHistory154 checkedWeights155 checkedRow155
theorem original155 : poly coeffs155 = row 155 3 :=
  head_original (checkedHistory155)

theorem checkedHistory156 : HistoryOK 156 history156 :=
  historyPush checkedHistory155 checkedWeights156 checkedRow156
theorem original156 : poly coeffs156 = row 156 3 :=
  head_original (checkedHistory156)

theorem checkedHistory157 : HistoryOK 157 history157 :=
  historyPush checkedHistory156 checkedWeights157 checkedRow157
theorem original157 : poly coeffs157 = row 157 3 :=
  head_original (checkedHistory157)

theorem checkedHistory158 : HistoryOK 158 history158 :=
  historyPush checkedHistory157 checkedWeights158 checkedRow158
theorem original158 : poly coeffs158 = row 158 3 :=
  head_original (checkedHistory158)

theorem checkedHistory159 : HistoryOK 159 history159 :=
  historyPush checkedHistory158 checkedWeights159 checkedRow159
theorem original159 : poly coeffs159 = row 159 3 :=
  head_original (checkedHistory159)


#print axioms original159

end OrderedPartitions.ThreePoleFinite
