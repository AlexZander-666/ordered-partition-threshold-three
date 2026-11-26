import OrderedPartitions.ThreePoleFiniteData.Roots056
import OrderedPartitions.ThreePoleFiniteData.Roots064

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair56Gap1 :
    RootTracking.OrderedPair (56/3) (row 56 3) (row 57 3) :=
  rise_pair (by decide) root56 root57 (by decide +kernel)

theorem pair56Gap2 :
    RootTracking.OrderedPair (56/3) (row 56 3) (row 58 3) :=
  rise_pair (by decide) root56 root58 (by decide +kernel)

theorem pair56Gap3 :
    RootTracking.OrderedPair (56/3) (row 56 3) (row 59 3) :=
  rise_pair (by decide) root56 root59 (by decide +kernel)

theorem pair57Gap1 :
    RootTracking.OrderedPair (57/3) (row 57 3) (row 58 3) :=
  stay_pair (by decide) root57 root58 (by decide +kernel)

theorem pair57Gap2 :
    RootTracking.OrderedPair (57/3) (row 57 3) (row 59 3) :=
  stay_pair (by decide) root57 root59 (by decide +kernel)

theorem pair57Gap3 :
    RootTracking.OrderedPair (57/3) (row 57 3) (row 60 3) :=
  rise_pair (by decide) root57 root60 (by decide +kernel)

theorem pair58Gap1 :
    RootTracking.OrderedPair (58/3) (row 58 3) (row 59 3) :=
  stay_pair (by decide) root58 root59 (by decide +kernel)

theorem pair58Gap2 :
    RootTracking.OrderedPair (58/3) (row 58 3) (row 60 3) :=
  rise_pair (by decide) root58 root60 (by decide +kernel)

theorem pair58Gap3 :
    RootTracking.OrderedPair (58/3) (row 58 3) (row 61 3) :=
  rise_pair (by decide) root58 root61 (by decide +kernel)

theorem pair59Gap1 :
    RootTracking.OrderedPair (59/3) (row 59 3) (row 60 3) :=
  rise_pair (by decide) root59 root60 (by decide +kernel)

theorem pair59Gap2 :
    RootTracking.OrderedPair (59/3) (row 59 3) (row 61 3) :=
  rise_pair (by decide) root59 root61 (by decide +kernel)

theorem pair59Gap3 :
    RootTracking.OrderedPair (59/3) (row 59 3) (row 62 3) :=
  rise_pair (by decide) root59 root62 (by decide +kernel)

theorem pair60Gap1 :
    RootTracking.OrderedPair (60/3) (row 60 3) (row 61 3) :=
  stay_pair (by decide) root60 root61 (by decide +kernel)

theorem pair60Gap2 :
    RootTracking.OrderedPair (60/3) (row 60 3) (row 62 3) :=
  stay_pair (by decide) root60 root62 (by decide +kernel)

theorem pair60Gap3 :
    RootTracking.OrderedPair (60/3) (row 60 3) (row 63 3) :=
  rise_pair (by decide) root60 root63 (by decide +kernel)

theorem pair61Gap1 :
    RootTracking.OrderedPair (61/3) (row 61 3) (row 62 3) :=
  stay_pair (by decide) root61 root62 (by decide +kernel)

theorem pair61Gap2 :
    RootTracking.OrderedPair (61/3) (row 61 3) (row 63 3) :=
  rise_pair (by decide) root61 root63 (by decide +kernel)

theorem pair61Gap3 :
    RootTracking.OrderedPair (61/3) (row 61 3) (row 64 3) :=
  rise_pair (by decide) root61 root64 (by decide +kernel)

theorem pair62Gap1 :
    RootTracking.OrderedPair (62/3) (row 62 3) (row 63 3) :=
  rise_pair (by decide) root62 root63 (by decide +kernel)

theorem pair62Gap2 :
    RootTracking.OrderedPair (62/3) (row 62 3) (row 64 3) :=
  rise_pair (by decide) root62 root64 (by decide +kernel)

theorem pair62Gap3 :
    RootTracking.OrderedPair (62/3) (row 62 3) (row 65 3) :=
  rise_pair (by decide) root62 root65 (by decide +kernel)

theorem pair63Gap1 :
    RootTracking.OrderedPair (63/3) (row 63 3) (row 64 3) :=
  stay_pair (by decide) root63 root64 (by decide +kernel)

theorem pair63Gap2 :
    RootTracking.OrderedPair (63/3) (row 63 3) (row 65 3) :=
  stay_pair (by decide) root63 root65 (by decide +kernel)

theorem pair63Gap3 :
    RootTracking.OrderedPair (63/3) (row 63 3) (row 66 3) :=
  rise_pair (by decide) root63 root66 (by decide +kernel)

theorem range56Gap1 (n : ℕ) (lo : 56 ≤ n) (hi : n ≤ 63) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair56Gap1
  · exact pair57Gap1
  · exact pair58Gap1
  · exact pair59Gap1
  · exact pair60Gap1
  · exact pair61Gap1
  · exact pair62Gap1
  · exact pair63Gap1

theorem range56Gap2 (n : ℕ) (lo : 56 ≤ n) (hi : n ≤ 63) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair56Gap2
  · exact pair57Gap2
  · exact pair58Gap2
  · exact pair59Gap2
  · exact pair60Gap2
  · exact pair61Gap2
  · exact pair62Gap2
  · exact pair63Gap2

theorem range56Gap3 (n : ℕ) (lo : 56 ≤ n) (hi : n ≤ 63) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair56Gap3
  · exact pair57Gap3
  · exact pair58Gap3
  · exact pair59Gap3
  · exact pair60Gap3
  · exact pair61Gap3
  · exact pair62Gap3
  · exact pair63Gap3


#print axioms range56Gap1
#print axioms range56Gap2
#print axioms range56Gap3

end OrderedPartitions.ThreePoleFinite
