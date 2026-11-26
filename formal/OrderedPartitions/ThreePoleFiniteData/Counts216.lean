import OrderedPartitions.ThreePoleFiniteData.Arithmetic216
import OrderedPartitions.ThreePoleFiniteData.Counts208

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory216 : HistoryOK 216 history216 :=
  historyPush checkedHistory215 checkedWeights216 checkedRow216
theorem original216 : poly coeffs216 = row 216 3 :=
  head_original (checkedHistory216)

theorem checkedHistory217 : HistoryOK 217 history217 :=
  historyPush checkedHistory216 checkedWeights217 checkedRow217
theorem original217 : poly coeffs217 = row 217 3 :=
  head_original (checkedHistory217)

theorem checkedHistory218 : HistoryOK 218 history218 :=
  historyPush checkedHistory217 checkedWeights218 checkedRow218
theorem original218 : poly coeffs218 = row 218 3 :=
  head_original (checkedHistory218)

theorem checkedHistory219 : HistoryOK 219 history219 :=
  historyPush checkedHistory218 checkedWeights219 checkedRow219
theorem original219 : poly coeffs219 = row 219 3 :=
  head_original (checkedHistory219)

theorem checkedHistory220 : HistoryOK 220 history220 :=
  historyPush checkedHistory219 checkedWeights220 checkedRow220
theorem original220 : poly coeffs220 = row 220 3 :=
  head_original (checkedHistory220)

theorem checkedHistory221 : HistoryOK 221 history221 :=
  historyPush checkedHistory220 checkedWeights221 checkedRow221
theorem original221 : poly coeffs221 = row 221 3 :=
  head_original (checkedHistory221)

theorem checkedHistory222 : HistoryOK 222 history222 :=
  historyPush checkedHistory221 checkedWeights222 checkedRow222
theorem original222 : poly coeffs222 = row 222 3 :=
  head_original (checkedHistory222)

theorem checkedHistory223 : HistoryOK 223 history223 :=
  historyPush checkedHistory222 checkedWeights223 checkedRow223
theorem original223 : poly coeffs223 = row 223 3 :=
  head_original (checkedHistory223)


#print axioms original223

end OrderedPartitions.ThreePoleFinite
