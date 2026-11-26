import OrderedPartitions.ThreePoleFiniteData.Arithmetic208
import OrderedPartitions.ThreePoleFiniteData.Counts200

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory208 : HistoryOK 208 history208 :=
  historyPush checkedHistory207 checkedWeights208 checkedRow208
theorem original208 : poly coeffs208 = row 208 3 :=
  head_original (checkedHistory208)

theorem checkedHistory209 : HistoryOK 209 history209 :=
  historyPush checkedHistory208 checkedWeights209 checkedRow209
theorem original209 : poly coeffs209 = row 209 3 :=
  head_original (checkedHistory209)

theorem checkedHistory210 : HistoryOK 210 history210 :=
  historyPush checkedHistory209 checkedWeights210 checkedRow210
theorem original210 : poly coeffs210 = row 210 3 :=
  head_original (checkedHistory210)

theorem checkedHistory211 : HistoryOK 211 history211 :=
  historyPush checkedHistory210 checkedWeights211 checkedRow211
theorem original211 : poly coeffs211 = row 211 3 :=
  head_original (checkedHistory211)

theorem checkedHistory212 : HistoryOK 212 history212 :=
  historyPush checkedHistory211 checkedWeights212 checkedRow212
theorem original212 : poly coeffs212 = row 212 3 :=
  head_original (checkedHistory212)

theorem checkedHistory213 : HistoryOK 213 history213 :=
  historyPush checkedHistory212 checkedWeights213 checkedRow213
theorem original213 : poly coeffs213 = row 213 3 :=
  head_original (checkedHistory213)

theorem checkedHistory214 : HistoryOK 214 history214 :=
  historyPush checkedHistory213 checkedWeights214 checkedRow214
theorem original214 : poly coeffs214 = row 214 3 :=
  head_original (checkedHistory214)

theorem checkedHistory215 : HistoryOK 215 history215 :=
  historyPush checkedHistory214 checkedWeights215 checkedRow215
theorem original215 : poly coeffs215 = row 215 3 :=
  head_original (checkedHistory215)


#print axioms original215

end OrderedPartitions.ThreePoleFinite
