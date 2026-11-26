import OrderedPartitions.ThreePoleFiniteData.Arithmetic048
import OrderedPartitions.ThreePoleFiniteData.Counts040

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory48 : HistoryOK 48 history48 :=
  historyPush checkedHistory47 checkedWeights48 checkedRow48
theorem original48 : poly coeffs48 = row 48 3 :=
  head_original (checkedHistory48)

theorem checkedHistory49 : HistoryOK 49 history49 :=
  historyPush checkedHistory48 checkedWeights49 checkedRow49
theorem original49 : poly coeffs49 = row 49 3 :=
  head_original (checkedHistory49)

theorem checkedHistory50 : HistoryOK 50 history50 :=
  historyPush checkedHistory49 checkedWeights50 checkedRow50
theorem original50 : poly coeffs50 = row 50 3 :=
  head_original (checkedHistory50)

theorem checkedHistory51 : HistoryOK 51 history51 :=
  historyPush checkedHistory50 checkedWeights51 checkedRow51
theorem original51 : poly coeffs51 = row 51 3 :=
  head_original (checkedHistory51)

theorem checkedHistory52 : HistoryOK 52 history52 :=
  historyPush checkedHistory51 checkedWeights52 checkedRow52
theorem original52 : poly coeffs52 = row 52 3 :=
  head_original (checkedHistory52)

theorem checkedHistory53 : HistoryOK 53 history53 :=
  historyPush checkedHistory52 checkedWeights53 checkedRow53
theorem original53 : poly coeffs53 = row 53 3 :=
  head_original (checkedHistory53)

theorem checkedHistory54 : HistoryOK 54 history54 :=
  historyPush checkedHistory53 checkedWeights54 checkedRow54
theorem original54 : poly coeffs54 = row 54 3 :=
  head_original (checkedHistory54)

theorem checkedHistory55 : HistoryOK 55 history55 :=
  historyPush checkedHistory54 checkedWeights55 checkedRow55
theorem original55 : poly coeffs55 = row 55 3 :=
  head_original (checkedHistory55)


#print axioms original55

end OrderedPartitions.ThreePoleFinite
