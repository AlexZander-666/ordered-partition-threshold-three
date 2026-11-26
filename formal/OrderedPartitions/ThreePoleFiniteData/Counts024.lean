import OrderedPartitions.ThreePoleFiniteData.Arithmetic024
import OrderedPartitions.ThreePoleFiniteData.Counts016

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory24 : HistoryOK 24 history24 :=
  historyPush checkedHistory23 checkedWeights24 checkedRow24
theorem original24 : poly coeffs24 = row 24 3 :=
  head_original (checkedHistory24)

theorem checkedHistory25 : HistoryOK 25 history25 :=
  historyPush checkedHistory24 checkedWeights25 checkedRow25
theorem original25 : poly coeffs25 = row 25 3 :=
  head_original (checkedHistory25)

theorem checkedHistory26 : HistoryOK 26 history26 :=
  historyPush checkedHistory25 checkedWeights26 checkedRow26
theorem original26 : poly coeffs26 = row 26 3 :=
  head_original (checkedHistory26)

theorem checkedHistory27 : HistoryOK 27 history27 :=
  historyPush checkedHistory26 checkedWeights27 checkedRow27
theorem original27 : poly coeffs27 = row 27 3 :=
  head_original (checkedHistory27)

theorem checkedHistory28 : HistoryOK 28 history28 :=
  historyPush checkedHistory27 checkedWeights28 checkedRow28
theorem original28 : poly coeffs28 = row 28 3 :=
  head_original (checkedHistory28)

theorem checkedHistory29 : HistoryOK 29 history29 :=
  historyPush checkedHistory28 checkedWeights29 checkedRow29
theorem original29 : poly coeffs29 = row 29 3 :=
  head_original (checkedHistory29)

theorem checkedHistory30 : HistoryOK 30 history30 :=
  historyPush checkedHistory29 checkedWeights30 checkedRow30
theorem original30 : poly coeffs30 = row 30 3 :=
  head_original (checkedHistory30)

theorem checkedHistory31 : HistoryOK 31 history31 :=
  historyPush checkedHistory30 checkedWeights31 checkedRow31
theorem original31 : poly coeffs31 = row 31 3 :=
  head_original (checkedHistory31)


#print axioms original31

end OrderedPartitions.ThreePoleFinite
