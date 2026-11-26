import OrderedPartitions.ThreePoleFiniteData.Roots072
import OrderedPartitions.ThreePoleFiniteData.Roots080

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair72Gap1 :
    RootTracking.OrderedPair (72/3) (row 72 3) (row 73 3) :=
  stay_pair (by decide) root72 root73 (by decide +kernel)

theorem pair72Gap2 :
    RootTracking.OrderedPair (72/3) (row 72 3) (row 74 3) :=
  stay_pair (by decide) root72 root74 (by decide +kernel)

theorem pair72Gap3 :
    RootTracking.OrderedPair (72/3) (row 72 3) (row 75 3) :=
  rise_pair (by decide) root72 root75 (by decide +kernel)

theorem pair73Gap1 :
    RootTracking.OrderedPair (73/3) (row 73 3) (row 74 3) :=
  stay_pair (by decide) root73 root74 (by decide +kernel)

theorem pair73Gap2 :
    RootTracking.OrderedPair (73/3) (row 73 3) (row 75 3) :=
  rise_pair (by decide) root73 root75 (by decide +kernel)

theorem pair73Gap3 :
    RootTracking.OrderedPair (73/3) (row 73 3) (row 76 3) :=
  rise_pair (by decide) root73 root76 (by decide +kernel)

theorem pair74Gap1 :
    RootTracking.OrderedPair (74/3) (row 74 3) (row 75 3) :=
  rise_pair (by decide) root74 root75 (by decide +kernel)

theorem pair74Gap2 :
    RootTracking.OrderedPair (74/3) (row 74 3) (row 76 3) :=
  rise_pair (by decide) root74 root76 (by decide +kernel)

theorem pair74Gap3 :
    RootTracking.OrderedPair (74/3) (row 74 3) (row 77 3) :=
  rise_pair (by decide) root74 root77 (by decide +kernel)

theorem pair75Gap1 :
    RootTracking.OrderedPair (75/3) (row 75 3) (row 76 3) :=
  stay_pair (by decide) root75 root76 (by decide +kernel)

theorem pair75Gap2 :
    RootTracking.OrderedPair (75/3) (row 75 3) (row 77 3) :=
  stay_pair (by decide) root75 root77 (by decide +kernel)

theorem pair75Gap3 :
    RootTracking.OrderedPair (75/3) (row 75 3) (row 78 3) :=
  rise_pair (by decide) root75 root78 (by decide +kernel)

theorem pair76Gap1 :
    RootTracking.OrderedPair (76/3) (row 76 3) (row 77 3) :=
  stay_pair (by decide) root76 root77 (by decide +kernel)

theorem pair76Gap2 :
    RootTracking.OrderedPair (76/3) (row 76 3) (row 78 3) :=
  rise_pair (by decide) root76 root78 (by decide +kernel)

theorem pair76Gap3 :
    RootTracking.OrderedPair (76/3) (row 76 3) (row 79 3) :=
  rise_pair (by decide) root76 root79 (by decide +kernel)

theorem pair77Gap1 :
    RootTracking.OrderedPair (77/3) (row 77 3) (row 78 3) :=
  rise_pair (by decide) root77 root78 (by decide +kernel)

theorem pair77Gap2 :
    RootTracking.OrderedPair (77/3) (row 77 3) (row 79 3) :=
  rise_pair (by decide) root77 root79 (by decide +kernel)

theorem pair77Gap3 :
    RootTracking.OrderedPair (77/3) (row 77 3) (row 80 3) :=
  rise_pair (by decide) root77 root80 (by decide +kernel)

theorem pair78Gap1 :
    RootTracking.OrderedPair (78/3) (row 78 3) (row 79 3) :=
  stay_pair (by decide) root78 root79 (by decide +kernel)

theorem pair78Gap2 :
    RootTracking.OrderedPair (78/3) (row 78 3) (row 80 3) :=
  stay_pair (by decide) root78 root80 (by decide +kernel)

theorem pair78Gap3 :
    RootTracking.OrderedPair (78/3) (row 78 3) (row 81 3) :=
  rise_pair (by decide) root78 root81 (by decide +kernel)

theorem pair79Gap1 :
    RootTracking.OrderedPair (79/3) (row 79 3) (row 80 3) :=
  stay_pair (by decide) root79 root80 (by decide +kernel)

theorem pair79Gap2 :
    RootTracking.OrderedPair (79/3) (row 79 3) (row 81 3) :=
  rise_pair (by decide) root79 root81 (by decide +kernel)

theorem pair79Gap3 :
    RootTracking.OrderedPair (79/3) (row 79 3) (row 82 3) :=
  rise_pair (by decide) root79 root82 (by decide +kernel)

theorem range72Gap1 (n : ℕ) (lo : 72 ≤ n) (hi : n ≤ 79) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair72Gap1
  · exact pair73Gap1
  · exact pair74Gap1
  · exact pair75Gap1
  · exact pair76Gap1
  · exact pair77Gap1
  · exact pair78Gap1
  · exact pair79Gap1

theorem range72Gap2 (n : ℕ) (lo : 72 ≤ n) (hi : n ≤ 79) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair72Gap2
  · exact pair73Gap2
  · exact pair74Gap2
  · exact pair75Gap2
  · exact pair76Gap2
  · exact pair77Gap2
  · exact pair78Gap2
  · exact pair79Gap2

theorem range72Gap3 (n : ℕ) (lo : 72 ≤ n) (hi : n ≤ 79) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair72Gap3
  · exact pair73Gap3
  · exact pair74Gap3
  · exact pair75Gap3
  · exact pair76Gap3
  · exact pair77Gap3
  · exact pair78Gap3
  · exact pair79Gap3


#print axioms range72Gap1
#print axioms range72Gap2
#print axioms range72Gap3

end OrderedPartitions.ThreePoleFinite
