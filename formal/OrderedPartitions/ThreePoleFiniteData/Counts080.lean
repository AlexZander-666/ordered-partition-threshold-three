import OrderedPartitions.ThreePoleFiniteData.Arithmetic080
import OrderedPartitions.ThreePoleFiniteData.Counts072

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory80 : HistoryOK 80 history80 :=
  historyPush checkedHistory79 checkedWeights80 checkedRow80
theorem original80 : poly coeffs80 = row 80 3 :=
  head_original (checkedHistory80)

theorem checkedHistory81 : HistoryOK 81 history81 :=
  historyPush checkedHistory80 checkedWeights81 checkedRow81
theorem original81 : poly coeffs81 = row 81 3 :=
  head_original (checkedHistory81)

theorem checkedHistory82 : HistoryOK 82 history82 :=
  historyPush checkedHistory81 checkedWeights82 checkedRow82
theorem original82 : poly coeffs82 = row 82 3 :=
  head_original (checkedHistory82)

theorem checkedHistory83 : HistoryOK 83 history83 :=
  historyPush checkedHistory82 checkedWeights83 checkedRow83
theorem original83 : poly coeffs83 = row 83 3 :=
  head_original (checkedHistory83)

theorem checkedHistory84 : HistoryOK 84 history84 :=
  historyPush checkedHistory83 checkedWeights84 checkedRow84
theorem original84 : poly coeffs84 = row 84 3 :=
  head_original (checkedHistory84)

theorem checkedHistory85 : HistoryOK 85 history85 :=
  historyPush checkedHistory84 checkedWeights85 checkedRow85
theorem original85 : poly coeffs85 = row 85 3 :=
  head_original (checkedHistory85)

theorem checkedHistory86 : HistoryOK 86 history86 :=
  historyPush checkedHistory85 checkedWeights86 checkedRow86
theorem original86 : poly coeffs86 = row 86 3 :=
  head_original (checkedHistory86)

theorem checkedHistory87 : HistoryOK 87 history87 :=
  historyPush checkedHistory86 checkedWeights87 checkedRow87
theorem original87 : poly coeffs87 = row 87 3 :=
  head_original (checkedHistory87)


#print axioms original87

end OrderedPartitions.ThreePoleFinite
