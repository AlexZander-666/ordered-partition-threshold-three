import OrderedPartitions.ThreePoleFiniteData.Arithmetic056
import OrderedPartitions.ThreePoleFiniteData.Counts048

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory56 : HistoryOK 56 history56 :=
  historyPush checkedHistory55 checkedWeights56 checkedRow56
theorem original56 : poly coeffs56 = row 56 3 :=
  head_original (checkedHistory56)

theorem checkedHistory57 : HistoryOK 57 history57 :=
  historyPush checkedHistory56 checkedWeights57 checkedRow57
theorem original57 : poly coeffs57 = row 57 3 :=
  head_original (checkedHistory57)

theorem checkedHistory58 : HistoryOK 58 history58 :=
  historyPush checkedHistory57 checkedWeights58 checkedRow58
theorem original58 : poly coeffs58 = row 58 3 :=
  head_original (checkedHistory58)

theorem checkedHistory59 : HistoryOK 59 history59 :=
  historyPush checkedHistory58 checkedWeights59 checkedRow59
theorem original59 : poly coeffs59 = row 59 3 :=
  head_original (checkedHistory59)

theorem checkedHistory60 : HistoryOK 60 history60 :=
  historyPush checkedHistory59 checkedWeights60 checkedRow60
theorem original60 : poly coeffs60 = row 60 3 :=
  head_original (checkedHistory60)

theorem checkedHistory61 : HistoryOK 61 history61 :=
  historyPush checkedHistory60 checkedWeights61 checkedRow61
theorem original61 : poly coeffs61 = row 61 3 :=
  head_original (checkedHistory61)

theorem checkedHistory62 : HistoryOK 62 history62 :=
  historyPush checkedHistory61 checkedWeights62 checkedRow62
theorem original62 : poly coeffs62 = row 62 3 :=
  head_original (checkedHistory62)

theorem checkedHistory63 : HistoryOK 63 history63 :=
  historyPush checkedHistory62 checkedWeights63 checkedRow63
theorem original63 : poly coeffs63 = row 63 3 :=
  head_original (checkedHistory63)


#print axioms original63

end OrderedPartitions.ThreePoleFinite
