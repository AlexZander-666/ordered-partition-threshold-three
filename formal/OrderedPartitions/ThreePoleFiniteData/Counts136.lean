import OrderedPartitions.ThreePoleFiniteData.Arithmetic136
import OrderedPartitions.ThreePoleFiniteData.Counts128

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory136 : HistoryOK 136 history136 :=
  historyPush checkedHistory135 checkedWeights136 checkedRow136
theorem original136 : poly coeffs136 = row 136 3 :=
  head_original (checkedHistory136)

theorem checkedHistory137 : HistoryOK 137 history137 :=
  historyPush checkedHistory136 checkedWeights137 checkedRow137
theorem original137 : poly coeffs137 = row 137 3 :=
  head_original (checkedHistory137)

theorem checkedHistory138 : HistoryOK 138 history138 :=
  historyPush checkedHistory137 checkedWeights138 checkedRow138
theorem original138 : poly coeffs138 = row 138 3 :=
  head_original (checkedHistory138)

theorem checkedHistory139 : HistoryOK 139 history139 :=
  historyPush checkedHistory138 checkedWeights139 checkedRow139
theorem original139 : poly coeffs139 = row 139 3 :=
  head_original (checkedHistory139)

theorem checkedHistory140 : HistoryOK 140 history140 :=
  historyPush checkedHistory139 checkedWeights140 checkedRow140
theorem original140 : poly coeffs140 = row 140 3 :=
  head_original (checkedHistory140)

theorem checkedHistory141 : HistoryOK 141 history141 :=
  historyPush checkedHistory140 checkedWeights141 checkedRow141
theorem original141 : poly coeffs141 = row 141 3 :=
  head_original (checkedHistory141)

theorem checkedHistory142 : HistoryOK 142 history142 :=
  historyPush checkedHistory141 checkedWeights142 checkedRow142
theorem original142 : poly coeffs142 = row 142 3 :=
  head_original (checkedHistory142)

theorem checkedHistory143 : HistoryOK 143 history143 :=
  historyPush checkedHistory142 checkedWeights143 checkedRow143
theorem original143 : poly coeffs143 = row 143 3 :=
  head_original (checkedHistory143)


#print axioms original143

end OrderedPartitions.ThreePoleFinite
