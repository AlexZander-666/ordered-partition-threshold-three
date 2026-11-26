import OrderedPartitions.ThreePoleFiniteData.Arithmetic016
import OrderedPartitions.ThreePoleFiniteData.Counts008

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory16 : HistoryOK 16 history16 :=
  historyPush checkedHistory15 checkedWeights16 checkedRow16
theorem original16 : poly coeffs16 = row 16 3 :=
  head_original (checkedHistory16)

theorem checkedHistory17 : HistoryOK 17 history17 :=
  historyPush checkedHistory16 checkedWeights17 checkedRow17
theorem original17 : poly coeffs17 = row 17 3 :=
  head_original (checkedHistory17)

theorem checkedHistory18 : HistoryOK 18 history18 :=
  historyPush checkedHistory17 checkedWeights18 checkedRow18
theorem original18 : poly coeffs18 = row 18 3 :=
  head_original (checkedHistory18)

theorem checkedHistory19 : HistoryOK 19 history19 :=
  historyPush checkedHistory18 checkedWeights19 checkedRow19
theorem original19 : poly coeffs19 = row 19 3 :=
  head_original (checkedHistory19)

theorem checkedHistory20 : HistoryOK 20 history20 :=
  historyPush checkedHistory19 checkedWeights20 checkedRow20
theorem original20 : poly coeffs20 = row 20 3 :=
  head_original (checkedHistory20)

theorem checkedHistory21 : HistoryOK 21 history21 :=
  historyPush checkedHistory20 checkedWeights21 checkedRow21
theorem original21 : poly coeffs21 = row 21 3 :=
  head_original (checkedHistory21)

theorem checkedHistory22 : HistoryOK 22 history22 :=
  historyPush checkedHistory21 checkedWeights22 checkedRow22
theorem original22 : poly coeffs22 = row 22 3 :=
  head_original (checkedHistory22)

theorem checkedHistory23 : HistoryOK 23 history23 :=
  historyPush checkedHistory22 checkedWeights23 checkedRow23
theorem original23 : poly coeffs23 = row 23 3 :=
  head_original (checkedHistory23)


#print axioms original23

end OrderedPartitions.ThreePoleFinite
