import OrderedPartitions.ThreePoleFiniteData.Arithmetic224
import OrderedPartitions.ThreePoleFiniteData.Counts216

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory224 : HistoryOK 224 history224 :=
  historyPush checkedHistory223 checkedWeights224 checkedRow224
theorem original224 : poly coeffs224 = row 224 3 :=
  head_original (checkedHistory224)

theorem checkedHistory225 : HistoryOK 225 history225 :=
  historyPush checkedHistory224 checkedWeights225 checkedRow225
theorem original225 : poly coeffs225 = row 225 3 :=
  head_original (checkedHistory225)

theorem checkedHistory226 : HistoryOK 226 history226 :=
  historyPush checkedHistory225 checkedWeights226 checkedRow226
theorem original226 : poly coeffs226 = row 226 3 :=
  head_original (checkedHistory226)

theorem checkedHistory227 : HistoryOK 227 history227 :=
  historyPush checkedHistory226 checkedWeights227 checkedRow227
theorem original227 : poly coeffs227 = row 227 3 :=
  head_original (checkedHistory227)

theorem checkedHistory228 : HistoryOK 228 history228 :=
  historyPush checkedHistory227 checkedWeights228 checkedRow228
theorem original228 : poly coeffs228 = row 228 3 :=
  head_original (checkedHistory228)

theorem checkedHistory229 : HistoryOK 229 history229 :=
  historyPush checkedHistory228 checkedWeights229 checkedRow229
theorem original229 : poly coeffs229 = row 229 3 :=
  head_original (checkedHistory229)

theorem checkedHistory230 : HistoryOK 230 history230 :=
  historyPush checkedHistory229 checkedWeights230 checkedRow230
theorem original230 : poly coeffs230 = row 230 3 :=
  head_original (checkedHistory230)

theorem checkedHistory231 : HistoryOK 231 history231 :=
  historyPush checkedHistory230 checkedWeights231 checkedRow231
theorem original231 : poly coeffs231 = row 231 3 :=
  head_original (checkedHistory231)


#print axioms original231

end OrderedPartitions.ThreePoleFinite
