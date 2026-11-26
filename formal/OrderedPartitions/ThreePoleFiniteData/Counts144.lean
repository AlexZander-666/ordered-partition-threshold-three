import OrderedPartitions.ThreePoleFiniteData.Arithmetic144
import OrderedPartitions.ThreePoleFiniteData.Counts136

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory144 : HistoryOK 144 history144 :=
  historyPush checkedHistory143 checkedWeights144 checkedRow144
theorem original144 : poly coeffs144 = row 144 3 :=
  head_original (checkedHistory144)

theorem checkedHistory145 : HistoryOK 145 history145 :=
  historyPush checkedHistory144 checkedWeights145 checkedRow145
theorem original145 : poly coeffs145 = row 145 3 :=
  head_original (checkedHistory145)

theorem checkedHistory146 : HistoryOK 146 history146 :=
  historyPush checkedHistory145 checkedWeights146 checkedRow146
theorem original146 : poly coeffs146 = row 146 3 :=
  head_original (checkedHistory146)

theorem checkedHistory147 : HistoryOK 147 history147 :=
  historyPush checkedHistory146 checkedWeights147 checkedRow147
theorem original147 : poly coeffs147 = row 147 3 :=
  head_original (checkedHistory147)

theorem checkedHistory148 : HistoryOK 148 history148 :=
  historyPush checkedHistory147 checkedWeights148 checkedRow148
theorem original148 : poly coeffs148 = row 148 3 :=
  head_original (checkedHistory148)

theorem checkedHistory149 : HistoryOK 149 history149 :=
  historyPush checkedHistory148 checkedWeights149 checkedRow149
theorem original149 : poly coeffs149 = row 149 3 :=
  head_original (checkedHistory149)

theorem checkedHistory150 : HistoryOK 150 history150 :=
  historyPush checkedHistory149 checkedWeights150 checkedRow150
theorem original150 : poly coeffs150 = row 150 3 :=
  head_original (checkedHistory150)

theorem checkedHistory151 : HistoryOK 151 history151 :=
  historyPush checkedHistory150 checkedWeights151 checkedRow151
theorem original151 : poly coeffs151 = row 151 3 :=
  head_original (checkedHistory151)


#print axioms original151

end OrderedPartitions.ThreePoleFinite
