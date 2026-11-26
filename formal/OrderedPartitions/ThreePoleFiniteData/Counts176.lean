import OrderedPartitions.ThreePoleFiniteData.Arithmetic176
import OrderedPartitions.ThreePoleFiniteData.Counts168

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory176 : HistoryOK 176 history176 :=
  historyPush checkedHistory175 checkedWeights176 checkedRow176
theorem original176 : poly coeffs176 = row 176 3 :=
  head_original (checkedHistory176)

theorem checkedHistory177 : HistoryOK 177 history177 :=
  historyPush checkedHistory176 checkedWeights177 checkedRow177
theorem original177 : poly coeffs177 = row 177 3 :=
  head_original (checkedHistory177)

theorem checkedHistory178 : HistoryOK 178 history178 :=
  historyPush checkedHistory177 checkedWeights178 checkedRow178
theorem original178 : poly coeffs178 = row 178 3 :=
  head_original (checkedHistory178)

theorem checkedHistory179 : HistoryOK 179 history179 :=
  historyPush checkedHistory178 checkedWeights179 checkedRow179
theorem original179 : poly coeffs179 = row 179 3 :=
  head_original (checkedHistory179)

theorem checkedHistory180 : HistoryOK 180 history180 :=
  historyPush checkedHistory179 checkedWeights180 checkedRow180
theorem original180 : poly coeffs180 = row 180 3 :=
  head_original (checkedHistory180)

theorem checkedHistory181 : HistoryOK 181 history181 :=
  historyPush checkedHistory180 checkedWeights181 checkedRow181
theorem original181 : poly coeffs181 = row 181 3 :=
  head_original (checkedHistory181)

theorem checkedHistory182 : HistoryOK 182 history182 :=
  historyPush checkedHistory181 checkedWeights182 checkedRow182
theorem original182 : poly coeffs182 = row 182 3 :=
  head_original (checkedHistory182)

theorem checkedHistory183 : HistoryOK 183 history183 :=
  historyPush checkedHistory182 checkedWeights183 checkedRow183
theorem original183 : poly coeffs183 = row 183 3 :=
  head_original (checkedHistory183)


#print axioms original183

end OrderedPartitions.ThreePoleFinite
