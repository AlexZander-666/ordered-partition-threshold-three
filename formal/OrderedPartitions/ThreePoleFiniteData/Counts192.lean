import OrderedPartitions.ThreePoleFiniteData.Arithmetic192
import OrderedPartitions.ThreePoleFiniteData.Counts184

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory192 : HistoryOK 192 history192 :=
  historyPush checkedHistory191 checkedWeights192 checkedRow192
theorem original192 : poly coeffs192 = row 192 3 :=
  head_original (checkedHistory192)

theorem checkedHistory193 : HistoryOK 193 history193 :=
  historyPush checkedHistory192 checkedWeights193 checkedRow193
theorem original193 : poly coeffs193 = row 193 3 :=
  head_original (checkedHistory193)

theorem checkedHistory194 : HistoryOK 194 history194 :=
  historyPush checkedHistory193 checkedWeights194 checkedRow194
theorem original194 : poly coeffs194 = row 194 3 :=
  head_original (checkedHistory194)

theorem checkedHistory195 : HistoryOK 195 history195 :=
  historyPush checkedHistory194 checkedWeights195 checkedRow195
theorem original195 : poly coeffs195 = row 195 3 :=
  head_original (checkedHistory195)

theorem checkedHistory196 : HistoryOK 196 history196 :=
  historyPush checkedHistory195 checkedWeights196 checkedRow196
theorem original196 : poly coeffs196 = row 196 3 :=
  head_original (checkedHistory196)

theorem checkedHistory197 : HistoryOK 197 history197 :=
  historyPush checkedHistory196 checkedWeights197 checkedRow197
theorem original197 : poly coeffs197 = row 197 3 :=
  head_original (checkedHistory197)

theorem checkedHistory198 : HistoryOK 198 history198 :=
  historyPush checkedHistory197 checkedWeights198 checkedRow198
theorem original198 : poly coeffs198 = row 198 3 :=
  head_original (checkedHistory198)

theorem checkedHistory199 : HistoryOK 199 history199 :=
  historyPush checkedHistory198 checkedWeights199 checkedRow199
theorem original199 : poly coeffs199 = row 199 3 :=
  head_original (checkedHistory199)


#print axioms original199

end OrderedPartitions.ThreePoleFinite
