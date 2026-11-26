import OrderedPartitions.ThreePoleFiniteData.Arithmetic072
import OrderedPartitions.ThreePoleFiniteData.Counts064

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory72 : HistoryOK 72 history72 :=
  historyPush checkedHistory71 checkedWeights72 checkedRow72
theorem original72 : poly coeffs72 = row 72 3 :=
  head_original (checkedHistory72)

theorem checkedHistory73 : HistoryOK 73 history73 :=
  historyPush checkedHistory72 checkedWeights73 checkedRow73
theorem original73 : poly coeffs73 = row 73 3 :=
  head_original (checkedHistory73)

theorem checkedHistory74 : HistoryOK 74 history74 :=
  historyPush checkedHistory73 checkedWeights74 checkedRow74
theorem original74 : poly coeffs74 = row 74 3 :=
  head_original (checkedHistory74)

theorem checkedHistory75 : HistoryOK 75 history75 :=
  historyPush checkedHistory74 checkedWeights75 checkedRow75
theorem original75 : poly coeffs75 = row 75 3 :=
  head_original (checkedHistory75)

theorem checkedHistory76 : HistoryOK 76 history76 :=
  historyPush checkedHistory75 checkedWeights76 checkedRow76
theorem original76 : poly coeffs76 = row 76 3 :=
  head_original (checkedHistory76)

theorem checkedHistory77 : HistoryOK 77 history77 :=
  historyPush checkedHistory76 checkedWeights77 checkedRow77
theorem original77 : poly coeffs77 = row 77 3 :=
  head_original (checkedHistory77)

theorem checkedHistory78 : HistoryOK 78 history78 :=
  historyPush checkedHistory77 checkedWeights78 checkedRow78
theorem original78 : poly coeffs78 = row 78 3 :=
  head_original (checkedHistory78)

theorem checkedHistory79 : HistoryOK 79 history79 :=
  historyPush checkedHistory78 checkedWeights79 checkedRow79
theorem original79 : poly coeffs79 = row 79 3 :=
  head_original (checkedHistory79)


#print axioms original79

end OrderedPartitions.ThreePoleFinite
