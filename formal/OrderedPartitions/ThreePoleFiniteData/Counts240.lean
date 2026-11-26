import OrderedPartitions.ThreePoleFiniteData.Arithmetic240
import OrderedPartitions.ThreePoleFiniteData.Counts232

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory240 : HistoryOK 240 history240 :=
  historyPush checkedHistory239 checkedWeights240 checkedRow240
theorem original240 : poly coeffs240 = row 240 3 :=
  head_original (checkedHistory240)

theorem checkedHistory241 : HistoryOK 241 history241 :=
  historyPush checkedHistory240 checkedWeights241 checkedRow241
theorem original241 : poly coeffs241 = row 241 3 :=
  head_original (checkedHistory241)

theorem checkedHistory242 : HistoryOK 242 history242 :=
  historyPush checkedHistory241 checkedWeights242 checkedRow242
theorem original242 : poly coeffs242 = row 242 3 :=
  head_original (checkedHistory242)


#print axioms original242

end OrderedPartitions.ThreePoleFinite
