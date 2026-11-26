import OrderedPartitions.ThreePoleFiniteData.Arithmetic040
import OrderedPartitions.ThreePoleFiniteData.Counts032

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory40 : HistoryOK 40 history40 :=
  historyPush checkedHistory39 checkedWeights40 checkedRow40
theorem original40 : poly coeffs40 = row 40 3 :=
  head_original (checkedHistory40)

theorem checkedHistory41 : HistoryOK 41 history41 :=
  historyPush checkedHistory40 checkedWeights41 checkedRow41
theorem original41 : poly coeffs41 = row 41 3 :=
  head_original (checkedHistory41)

theorem checkedHistory42 : HistoryOK 42 history42 :=
  historyPush checkedHistory41 checkedWeights42 checkedRow42
theorem original42 : poly coeffs42 = row 42 3 :=
  head_original (checkedHistory42)

theorem checkedHistory43 : HistoryOK 43 history43 :=
  historyPush checkedHistory42 checkedWeights43 checkedRow43
theorem original43 : poly coeffs43 = row 43 3 :=
  head_original (checkedHistory43)

theorem checkedHistory44 : HistoryOK 44 history44 :=
  historyPush checkedHistory43 checkedWeights44 checkedRow44
theorem original44 : poly coeffs44 = row 44 3 :=
  head_original (checkedHistory44)

theorem checkedHistory45 : HistoryOK 45 history45 :=
  historyPush checkedHistory44 checkedWeights45 checkedRow45
theorem original45 : poly coeffs45 = row 45 3 :=
  head_original (checkedHistory45)

theorem checkedHistory46 : HistoryOK 46 history46 :=
  historyPush checkedHistory45 checkedWeights46 checkedRow46
theorem original46 : poly coeffs46 = row 46 3 :=
  head_original (checkedHistory46)

theorem checkedHistory47 : HistoryOK 47 history47 :=
  historyPush checkedHistory46 checkedWeights47 checkedRow47
theorem original47 : poly coeffs47 = row 47 3 :=
  head_original (checkedHistory47)


#print axioms original47

end OrderedPartitions.ThreePoleFinite
