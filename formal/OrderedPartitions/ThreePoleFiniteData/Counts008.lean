import OrderedPartitions.ThreePoleFiniteData.Arithmetic008
import OrderedPartitions.ThreePoleFiniteData.Counts000

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory8 : HistoryOK 8 history8 :=
  historyPush checkedHistory7 checkedWeights8 checkedRow8
theorem original8 : poly coeffs8 = row 8 3 :=
  head_original (checkedHistory8)

theorem checkedHistory9 : HistoryOK 9 history9 :=
  historyPush checkedHistory8 checkedWeights9 checkedRow9
theorem original9 : poly coeffs9 = row 9 3 :=
  head_original (checkedHistory9)

theorem checkedHistory10 : HistoryOK 10 history10 :=
  historyPush checkedHistory9 checkedWeights10 checkedRow10
theorem original10 : poly coeffs10 = row 10 3 :=
  head_original (checkedHistory10)

theorem checkedHistory11 : HistoryOK 11 history11 :=
  historyPush checkedHistory10 checkedWeights11 checkedRow11
theorem original11 : poly coeffs11 = row 11 3 :=
  head_original (checkedHistory11)

theorem checkedHistory12 : HistoryOK 12 history12 :=
  historyPush checkedHistory11 checkedWeights12 checkedRow12
theorem original12 : poly coeffs12 = row 12 3 :=
  head_original (checkedHistory12)

theorem checkedHistory13 : HistoryOK 13 history13 :=
  historyPush checkedHistory12 checkedWeights13 checkedRow13
theorem original13 : poly coeffs13 = row 13 3 :=
  head_original (checkedHistory13)

theorem checkedHistory14 : HistoryOK 14 history14 :=
  historyPush checkedHistory13 checkedWeights14 checkedRow14
theorem original14 : poly coeffs14 = row 14 3 :=
  head_original (checkedHistory14)

theorem checkedHistory15 : HistoryOK 15 history15 :=
  historyPush checkedHistory14 checkedWeights15 checkedRow15
theorem original15 : poly coeffs15 = row 15 3 :=
  head_original (checkedHistory15)


#print axioms original15

end OrderedPartitions.ThreePoleFinite
