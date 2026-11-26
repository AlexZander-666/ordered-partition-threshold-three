import OrderedPartitions.ThreePoleFiniteData.Arithmetic184
import OrderedPartitions.ThreePoleFiniteData.Counts176

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory184 : HistoryOK 184 history184 :=
  historyPush checkedHistory183 checkedWeights184 checkedRow184
theorem original184 : poly coeffs184 = row 184 3 :=
  head_original (checkedHistory184)

theorem checkedHistory185 : HistoryOK 185 history185 :=
  historyPush checkedHistory184 checkedWeights185 checkedRow185
theorem original185 : poly coeffs185 = row 185 3 :=
  head_original (checkedHistory185)

theorem checkedHistory186 : HistoryOK 186 history186 :=
  historyPush checkedHistory185 checkedWeights186 checkedRow186
theorem original186 : poly coeffs186 = row 186 3 :=
  head_original (checkedHistory186)

theorem checkedHistory187 : HistoryOK 187 history187 :=
  historyPush checkedHistory186 checkedWeights187 checkedRow187
theorem original187 : poly coeffs187 = row 187 3 :=
  head_original (checkedHistory187)

theorem checkedHistory188 : HistoryOK 188 history188 :=
  historyPush checkedHistory187 checkedWeights188 checkedRow188
theorem original188 : poly coeffs188 = row 188 3 :=
  head_original (checkedHistory188)

theorem checkedHistory189 : HistoryOK 189 history189 :=
  historyPush checkedHistory188 checkedWeights189 checkedRow189
theorem original189 : poly coeffs189 = row 189 3 :=
  head_original (checkedHistory189)

theorem checkedHistory190 : HistoryOK 190 history190 :=
  historyPush checkedHistory189 checkedWeights190 checkedRow190
theorem original190 : poly coeffs190 = row 190 3 :=
  head_original (checkedHistory190)

theorem checkedHistory191 : HistoryOK 191 history191 :=
  historyPush checkedHistory190 checkedWeights191 checkedRow191
theorem original191 : poly coeffs191 = row 191 3 :=
  head_original (checkedHistory191)


#print axioms original191

end OrderedPartitions.ThreePoleFinite
