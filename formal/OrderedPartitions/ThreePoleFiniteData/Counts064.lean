import OrderedPartitions.ThreePoleFiniteData.Arithmetic064
import OrderedPartitions.ThreePoleFiniteData.Counts056

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory64 : HistoryOK 64 history64 :=
  historyPush checkedHistory63 checkedWeights64 checkedRow64
theorem original64 : poly coeffs64 = row 64 3 :=
  head_original (checkedHistory64)

theorem checkedHistory65 : HistoryOK 65 history65 :=
  historyPush checkedHistory64 checkedWeights65 checkedRow65
theorem original65 : poly coeffs65 = row 65 3 :=
  head_original (checkedHistory65)

theorem checkedHistory66 : HistoryOK 66 history66 :=
  historyPush checkedHistory65 checkedWeights66 checkedRow66
theorem original66 : poly coeffs66 = row 66 3 :=
  head_original (checkedHistory66)

theorem checkedHistory67 : HistoryOK 67 history67 :=
  historyPush checkedHistory66 checkedWeights67 checkedRow67
theorem original67 : poly coeffs67 = row 67 3 :=
  head_original (checkedHistory67)

theorem checkedHistory68 : HistoryOK 68 history68 :=
  historyPush checkedHistory67 checkedWeights68 checkedRow68
theorem original68 : poly coeffs68 = row 68 3 :=
  head_original (checkedHistory68)

theorem checkedHistory69 : HistoryOK 69 history69 :=
  historyPush checkedHistory68 checkedWeights69 checkedRow69
theorem original69 : poly coeffs69 = row 69 3 :=
  head_original (checkedHistory69)

theorem checkedHistory70 : HistoryOK 70 history70 :=
  historyPush checkedHistory69 checkedWeights70 checkedRow70
theorem original70 : poly coeffs70 = row 70 3 :=
  head_original (checkedHistory70)

theorem checkedHistory71 : HistoryOK 71 history71 :=
  historyPush checkedHistory70 checkedWeights71 checkedRow71
theorem original71 : poly coeffs71 = row 71 3 :=
  head_original (checkedHistory71)


#print axioms original71

end OrderedPartitions.ThreePoleFinite
