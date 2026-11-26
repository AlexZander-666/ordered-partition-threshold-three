import OrderedPartitions.ThreePoleFiniteData.Arithmetic232
import OrderedPartitions.ThreePoleFiniteData.Counts224

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory232 : HistoryOK 232 history232 :=
  historyPush checkedHistory231 checkedWeights232 checkedRow232
theorem original232 : poly coeffs232 = row 232 3 :=
  head_original (checkedHistory232)

theorem checkedHistory233 : HistoryOK 233 history233 :=
  historyPush checkedHistory232 checkedWeights233 checkedRow233
theorem original233 : poly coeffs233 = row 233 3 :=
  head_original (checkedHistory233)

theorem checkedHistory234 : HistoryOK 234 history234 :=
  historyPush checkedHistory233 checkedWeights234 checkedRow234
theorem original234 : poly coeffs234 = row 234 3 :=
  head_original (checkedHistory234)

theorem checkedHistory235 : HistoryOK 235 history235 :=
  historyPush checkedHistory234 checkedWeights235 checkedRow235
theorem original235 : poly coeffs235 = row 235 3 :=
  head_original (checkedHistory235)

theorem checkedHistory236 : HistoryOK 236 history236 :=
  historyPush checkedHistory235 checkedWeights236 checkedRow236
theorem original236 : poly coeffs236 = row 236 3 :=
  head_original (checkedHistory236)

theorem checkedHistory237 : HistoryOK 237 history237 :=
  historyPush checkedHistory236 checkedWeights237 checkedRow237
theorem original237 : poly coeffs237 = row 237 3 :=
  head_original (checkedHistory237)

theorem checkedHistory238 : HistoryOK 238 history238 :=
  historyPush checkedHistory237 checkedWeights238 checkedRow238
theorem original238 : poly coeffs238 = row 238 3 :=
  head_original (checkedHistory238)

theorem checkedHistory239 : HistoryOK 239 history239 :=
  historyPush checkedHistory238 checkedWeights239 checkedRow239
theorem original239 : poly coeffs239 = row 239 3 :=
  head_original (checkedHistory239)


#print axioms original239

end OrderedPartitions.ThreePoleFinite
