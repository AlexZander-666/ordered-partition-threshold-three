import OrderedPartitions.ThreePoleFiniteData.Roots040
import OrderedPartitions.ThreePoleFiniteData.Roots048

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair40Gap1 :
    RootTracking.OrderedPair (40/3) (row 40 3) (row 41 3) :=
  stay_pair (by decide) root40 root41 (by decide +kernel)

theorem pair40Gap2 :
    RootTracking.OrderedPair (40/3) (row 40 3) (row 42 3) :=
  rise_pair (by decide) root40 root42 (by decide +kernel)

theorem pair40Gap3 :
    RootTracking.OrderedPair (40/3) (row 40 3) (row 43 3) :=
  rise_pair (by decide) root40 root43 (by decide +kernel)

theorem pair41Gap1 :
    RootTracking.OrderedPair (41/3) (row 41 3) (row 42 3) :=
  rise_pair (by decide) root41 root42 (by decide +kernel)

theorem pair41Gap2 :
    RootTracking.OrderedPair (41/3) (row 41 3) (row 43 3) :=
  rise_pair (by decide) root41 root43 (by decide +kernel)

theorem pair41Gap3 :
    RootTracking.OrderedPair (41/3) (row 41 3) (row 44 3) :=
  rise_pair (by decide) root41 root44 (by decide +kernel)

theorem pair42Gap1 :
    RootTracking.OrderedPair (42/3) (row 42 3) (row 43 3) :=
  stay_pair (by decide) root42 root43 (by decide +kernel)

theorem pair42Gap2 :
    RootTracking.OrderedPair (42/3) (row 42 3) (row 44 3) :=
  stay_pair (by decide) root42 root44 (by decide +kernel)

theorem pair42Gap3 :
    RootTracking.OrderedPair (42/3) (row 42 3) (row 45 3) :=
  rise_pair (by decide) root42 root45 (by decide +kernel)

theorem pair43Gap1 :
    RootTracking.OrderedPair (43/3) (row 43 3) (row 44 3) :=
  stay_pair (by decide) root43 root44 (by decide +kernel)

theorem pair43Gap2 :
    RootTracking.OrderedPair (43/3) (row 43 3) (row 45 3) :=
  rise_pair (by decide) root43 root45 (by decide +kernel)

theorem pair43Gap3 :
    RootTracking.OrderedPair (43/3) (row 43 3) (row 46 3) :=
  rise_pair (by decide) root43 root46 (by decide +kernel)

theorem pair44Gap1 :
    RootTracking.OrderedPair (44/3) (row 44 3) (row 45 3) :=
  rise_pair (by decide) root44 root45 (by decide +kernel)

theorem pair44Gap2 :
    RootTracking.OrderedPair (44/3) (row 44 3) (row 46 3) :=
  rise_pair (by decide) root44 root46 (by decide +kernel)

theorem pair44Gap3 :
    RootTracking.OrderedPair (44/3) (row 44 3) (row 47 3) :=
  rise_pair (by decide) root44 root47 (by decide +kernel)

theorem pair45Gap1 :
    RootTracking.OrderedPair (45/3) (row 45 3) (row 46 3) :=
  stay_pair (by decide) root45 root46 (by decide +kernel)

theorem pair45Gap2 :
    RootTracking.OrderedPair (45/3) (row 45 3) (row 47 3) :=
  stay_pair (by decide) root45 root47 (by decide +kernel)

theorem pair45Gap3 :
    RootTracking.OrderedPair (45/3) (row 45 3) (row 48 3) :=
  rise_pair (by decide) root45 root48 (by decide +kernel)

theorem pair46Gap1 :
    RootTracking.OrderedPair (46/3) (row 46 3) (row 47 3) :=
  stay_pair (by decide) root46 root47 (by decide +kernel)

theorem pair46Gap2 :
    RootTracking.OrderedPair (46/3) (row 46 3) (row 48 3) :=
  rise_pair (by decide) root46 root48 (by decide +kernel)

theorem pair46Gap3 :
    RootTracking.OrderedPair (46/3) (row 46 3) (row 49 3) :=
  rise_pair (by decide) root46 root49 (by decide +kernel)

theorem pair47Gap1 :
    RootTracking.OrderedPair (47/3) (row 47 3) (row 48 3) :=
  rise_pair (by decide) root47 root48 (by decide +kernel)

theorem pair47Gap2 :
    RootTracking.OrderedPair (47/3) (row 47 3) (row 49 3) :=
  rise_pair (by decide) root47 root49 (by decide +kernel)

theorem pair47Gap3 :
    RootTracking.OrderedPair (47/3) (row 47 3) (row 50 3) :=
  rise_pair (by decide) root47 root50 (by decide +kernel)

theorem range40Gap1 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair40Gap1
  · exact pair41Gap1
  · exact pair42Gap1
  · exact pair43Gap1
  · exact pair44Gap1
  · exact pair45Gap1
  · exact pair46Gap1
  · exact pair47Gap1

theorem range40Gap2 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair40Gap2
  · exact pair41Gap2
  · exact pair42Gap2
  · exact pair43Gap2
  · exact pair44Gap2
  · exact pair45Gap2
  · exact pair46Gap2
  · exact pair47Gap2

theorem range40Gap3 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair40Gap3
  · exact pair41Gap3
  · exact pair42Gap3
  · exact pair43Gap3
  · exact pair44Gap3
  · exact pair45Gap3
  · exact pair46Gap3
  · exact pair47Gap3


#print axioms range40Gap1
#print axioms range40Gap2
#print axioms range40Gap3

end OrderedPartitions.ThreePoleFinite
