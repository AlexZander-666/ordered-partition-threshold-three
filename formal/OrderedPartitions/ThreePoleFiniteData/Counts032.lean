import OrderedPartitions.ThreePoleFiniteData.Arithmetic032
import OrderedPartitions.ThreePoleFiniteData.Counts024

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory32 : HistoryOK 32 history32 :=
  historyPush checkedHistory31 checkedWeights32 checkedRow32
theorem original32 : poly coeffs32 = row 32 3 :=
  head_original (checkedHistory32)

theorem checkedHistory33 : HistoryOK 33 history33 :=
  historyPush checkedHistory32 checkedWeights33 checkedRow33
theorem original33 : poly coeffs33 = row 33 3 :=
  head_original (checkedHistory33)

theorem checkedHistory34 : HistoryOK 34 history34 :=
  historyPush checkedHistory33 checkedWeights34 checkedRow34
theorem original34 : poly coeffs34 = row 34 3 :=
  head_original (checkedHistory34)

theorem checkedHistory35 : HistoryOK 35 history35 :=
  historyPush checkedHistory34 checkedWeights35 checkedRow35
theorem original35 : poly coeffs35 = row 35 3 :=
  head_original (checkedHistory35)

theorem checkedHistory36 : HistoryOK 36 history36 :=
  historyPush checkedHistory35 checkedWeights36 checkedRow36
theorem original36 : poly coeffs36 = row 36 3 :=
  head_original (checkedHistory36)

theorem checkedHistory37 : HistoryOK 37 history37 :=
  historyPush checkedHistory36 checkedWeights37 checkedRow37
theorem original37 : poly coeffs37 = row 37 3 :=
  head_original (checkedHistory37)

theorem checkedHistory38 : HistoryOK 38 history38 :=
  historyPush checkedHistory37 checkedWeights38 checkedRow38
theorem original38 : poly coeffs38 = row 38 3 :=
  head_original (checkedHistory38)

theorem checkedHistory39 : HistoryOK 39 history39 :=
  historyPush checkedHistory38 checkedWeights39 checkedRow39
theorem original39 : poly coeffs39 = row 39 3 :=
  head_original (checkedHistory39)


#print axioms original39

end OrderedPartitions.ThreePoleFinite
