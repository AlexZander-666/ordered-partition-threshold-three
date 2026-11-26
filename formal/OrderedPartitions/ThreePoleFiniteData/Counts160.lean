import OrderedPartitions.ThreePoleFiniteData.Arithmetic160
import OrderedPartitions.ThreePoleFiniteData.Counts152

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory160 : HistoryOK 160 history160 :=
  historyPush checkedHistory159 checkedWeights160 checkedRow160
theorem original160 : poly coeffs160 = row 160 3 :=
  head_original (checkedHistory160)

theorem checkedHistory161 : HistoryOK 161 history161 :=
  historyPush checkedHistory160 checkedWeights161 checkedRow161
theorem original161 : poly coeffs161 = row 161 3 :=
  head_original (checkedHistory161)

theorem checkedHistory162 : HistoryOK 162 history162 :=
  historyPush checkedHistory161 checkedWeights162 checkedRow162
theorem original162 : poly coeffs162 = row 162 3 :=
  head_original (checkedHistory162)

theorem checkedHistory163 : HistoryOK 163 history163 :=
  historyPush checkedHistory162 checkedWeights163 checkedRow163
theorem original163 : poly coeffs163 = row 163 3 :=
  head_original (checkedHistory163)

theorem checkedHistory164 : HistoryOK 164 history164 :=
  historyPush checkedHistory163 checkedWeights164 checkedRow164
theorem original164 : poly coeffs164 = row 164 3 :=
  head_original (checkedHistory164)

theorem checkedHistory165 : HistoryOK 165 history165 :=
  historyPush checkedHistory164 checkedWeights165 checkedRow165
theorem original165 : poly coeffs165 = row 165 3 :=
  head_original (checkedHistory165)

theorem checkedHistory166 : HistoryOK 166 history166 :=
  historyPush checkedHistory165 checkedWeights166 checkedRow166
theorem original166 : poly coeffs166 = row 166 3 :=
  head_original (checkedHistory166)

theorem checkedHistory167 : HistoryOK 167 history167 :=
  historyPush checkedHistory166 checkedWeights167 checkedRow167
theorem original167 : poly coeffs167 = row 167 3 :=
  head_original (checkedHistory167)


#print axioms original167

end OrderedPartitions.ThreePoleFinite
