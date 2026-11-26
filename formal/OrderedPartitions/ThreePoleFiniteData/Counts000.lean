import OrderedPartitions.ThreePoleFiniteData.Arithmetic000

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory0 : HistoryOK 0 history0 := historyInitial
theorem original0 : poly coeffs0 = row 0 3 := head_original checkedHistory0

theorem checkedHistory1 : HistoryOK 1 history1 :=
  historyPush checkedHistory0 checkedWeights1 checkedRow1
theorem original1 : poly coeffs1 = row 1 3 :=
  head_original (checkedHistory1)

theorem checkedHistory2 : HistoryOK 2 history2 :=
  historyPush checkedHistory1 checkedWeights2 checkedRow2
theorem original2 : poly coeffs2 = row 2 3 :=
  head_original (checkedHistory2)

theorem checkedHistory3 : HistoryOK 3 history3 :=
  historyPush checkedHistory2 checkedWeights3 checkedRow3
theorem original3 : poly coeffs3 = row 3 3 :=
  head_original (checkedHistory3)

theorem checkedHistory4 : HistoryOK 4 history4 :=
  historyPush checkedHistory3 checkedWeights4 checkedRow4
theorem original4 : poly coeffs4 = row 4 3 :=
  head_original (checkedHistory4)

theorem checkedHistory5 : HistoryOK 5 history5 :=
  historyPush checkedHistory4 checkedWeights5 checkedRow5
theorem original5 : poly coeffs5 = row 5 3 :=
  head_original (checkedHistory5)

theorem checkedHistory6 : HistoryOK 6 history6 :=
  historyPush checkedHistory5 checkedWeights6 checkedRow6
theorem original6 : poly coeffs6 = row 6 3 :=
  head_original (checkedHistory6)

theorem checkedHistory7 : HistoryOK 7 history7 :=
  historyPush checkedHistory6 checkedWeights7 checkedRow7
theorem original7 : poly coeffs7 = row 7 3 :=
  head_original (checkedHistory7)


#print axioms original7

end OrderedPartitions.ThreePoleFinite
