import OrderedPartitions.ThreePoleFiniteData.Arithmetic168
import OrderedPartitions.ThreePoleFiniteData.Counts160

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory168 : HistoryOK 168 history168 :=
  historyPush checkedHistory167 checkedWeights168 checkedRow168
theorem original168 : poly coeffs168 = row 168 3 :=
  head_original (checkedHistory168)

theorem checkedHistory169 : HistoryOK 169 history169 :=
  historyPush checkedHistory168 checkedWeights169 checkedRow169
theorem original169 : poly coeffs169 = row 169 3 :=
  head_original (checkedHistory169)

theorem checkedHistory170 : HistoryOK 170 history170 :=
  historyPush checkedHistory169 checkedWeights170 checkedRow170
theorem original170 : poly coeffs170 = row 170 3 :=
  head_original (checkedHistory170)

theorem checkedHistory171 : HistoryOK 171 history171 :=
  historyPush checkedHistory170 checkedWeights171 checkedRow171
theorem original171 : poly coeffs171 = row 171 3 :=
  head_original (checkedHistory171)

theorem checkedHistory172 : HistoryOK 172 history172 :=
  historyPush checkedHistory171 checkedWeights172 checkedRow172
theorem original172 : poly coeffs172 = row 172 3 :=
  head_original (checkedHistory172)

theorem checkedHistory173 : HistoryOK 173 history173 :=
  historyPush checkedHistory172 checkedWeights173 checkedRow173
theorem original173 : poly coeffs173 = row 173 3 :=
  head_original (checkedHistory173)

theorem checkedHistory174 : HistoryOK 174 history174 :=
  historyPush checkedHistory173 checkedWeights174 checkedRow174
theorem original174 : poly coeffs174 = row 174 3 :=
  head_original (checkedHistory174)

theorem checkedHistory175 : HistoryOK 175 history175 :=
  historyPush checkedHistory174 checkedWeights175 checkedRow175
theorem original175 : poly coeffs175 = row 175 3 :=
  head_original (checkedHistory175)


#print axioms original175

end OrderedPartitions.ThreePoleFinite
