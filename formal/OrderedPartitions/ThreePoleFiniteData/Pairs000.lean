import OrderedPartitions.ThreePoleFiniteData.Roots000
import OrderedPartitions.ThreePoleFiniteData.Roots008

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair0Gap1 :
    RootTracking.OrderedPair (0/3) (row 0 3) (row 1 3) :=
  stay_pair (by decide) root0 root1 (by decide +kernel)

theorem pair0Gap2 :
    RootTracking.OrderedPair (0/3) (row 0 3) (row 2 3) :=
  stay_pair (by decide) root0 root2 (by decide +kernel)

theorem pair0Gap3 :
    RootTracking.OrderedPair (0/3) (row 0 3) (row 3 3) :=
  rise_pair (by decide) root0 root3 (by decide +kernel)

theorem pair1Gap1 :
    RootTracking.OrderedPair (1/3) (row 1 3) (row 2 3) :=
  stay_pair (by decide) root1 root2 (by decide +kernel)

theorem pair1Gap2 :
    RootTracking.OrderedPair (1/3) (row 1 3) (row 3 3) :=
  rise_pair (by decide) root1 root3 (by decide +kernel)

theorem pair1Gap3 :
    RootTracking.OrderedPair (1/3) (row 1 3) (row 4 3) :=
  rise_pair (by decide) root1 root4 (by decide +kernel)

theorem pair2Gap1 :
    RootTracking.OrderedPair (2/3) (row 2 3) (row 3 3) :=
  rise_pair (by decide) root2 root3 (by decide +kernel)

theorem pair2Gap2 :
    RootTracking.OrderedPair (2/3) (row 2 3) (row 4 3) :=
  rise_pair (by decide) root2 root4 (by decide +kernel)

theorem pair2Gap3 :
    RootTracking.OrderedPair (2/3) (row 2 3) (row 5 3) :=
  rise_pair (by decide) root2 root5 (by decide +kernel)

theorem pair3Gap1 :
    RootTracking.OrderedPair (3/3) (row 3 3) (row 4 3) :=
  stay_pair (by decide) root3 root4 (by decide +kernel)

theorem pair3Gap2 :
    RootTracking.OrderedPair (3/3) (row 3 3) (row 5 3) :=
  stay_pair (by decide) root3 root5 (by decide +kernel)

theorem pair3Gap3 :
    RootTracking.OrderedPair (3/3) (row 3 3) (row 6 3) :=
  rise_pair (by decide) root3 root6 (by decide +kernel)

theorem pair4Gap1 :
    RootTracking.OrderedPair (4/3) (row 4 3) (row 5 3) :=
  stay_pair (by decide) root4 root5 (by decide +kernel)

theorem pair4Gap2 :
    RootTracking.OrderedPair (4/3) (row 4 3) (row 6 3) :=
  rise_pair (by decide) root4 root6 (by decide +kernel)

theorem pair4Gap3 :
    RootTracking.OrderedPair (4/3) (row 4 3) (row 7 3) :=
  rise_pair (by decide) root4 root7 (by decide +kernel)

theorem pair5Gap1 :
    RootTracking.OrderedPair (5/3) (row 5 3) (row 6 3) :=
  rise_pair (by decide) root5 root6 (by decide +kernel)

theorem pair5Gap2 :
    RootTracking.OrderedPair (5/3) (row 5 3) (row 7 3) :=
  rise_pair (by decide) root5 root7 (by decide +kernel)

theorem pair5Gap3 :
    RootTracking.OrderedPair (5/3) (row 5 3) (row 8 3) :=
  rise_pair (by decide) root5 root8 (by decide +kernel)

theorem pair6Gap1 :
    RootTracking.OrderedPair (6/3) (row 6 3) (row 7 3) :=
  stay_pair (by decide) root6 root7 (by decide +kernel)

theorem pair6Gap2 :
    RootTracking.OrderedPair (6/3) (row 6 3) (row 8 3) :=
  stay_pair (by decide) root6 root8 (by decide +kernel)

theorem pair6Gap3 :
    RootTracking.OrderedPair (6/3) (row 6 3) (row 9 3) :=
  rise_pair (by decide) root6 root9 (by decide +kernel)

theorem pair7Gap1 :
    RootTracking.OrderedPair (7/3) (row 7 3) (row 8 3) :=
  stay_pair (by decide) root7 root8 (by decide +kernel)

theorem pair7Gap2 :
    RootTracking.OrderedPair (7/3) (row 7 3) (row 9 3) :=
  rise_pair (by decide) root7 root9 (by decide +kernel)

theorem pair7Gap3 :
    RootTracking.OrderedPair (7/3) (row 7 3) (row 10 3) :=
  rise_pair (by decide) root7 root10 (by decide +kernel)

theorem range0Gap1 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair0Gap1
  · exact pair1Gap1
  · exact pair2Gap1
  · exact pair3Gap1
  · exact pair4Gap1
  · exact pair5Gap1
  · exact pair6Gap1
  · exact pair7Gap1

theorem range0Gap2 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair0Gap2
  · exact pair1Gap2
  · exact pair2Gap2
  · exact pair3Gap2
  · exact pair4Gap2
  · exact pair5Gap2
  · exact pair6Gap2
  · exact pair7Gap2

theorem range0Gap3 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair0Gap3
  · exact pair1Gap3
  · exact pair2Gap3
  · exact pair3Gap3
  · exact pair4Gap3
  · exact pair5Gap3
  · exact pair6Gap3
  · exact pair7Gap3


#print axioms range0Gap1
#print axioms range0Gap2
#print axioms range0Gap3

end OrderedPartitions.ThreePoleFinite
