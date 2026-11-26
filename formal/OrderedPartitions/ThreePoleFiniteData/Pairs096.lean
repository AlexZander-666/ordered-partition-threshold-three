import OrderedPartitions.ThreePoleFiniteData.Roots096
import OrderedPartitions.ThreePoleFiniteData.Roots104

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair96Gap1 :
    RootTracking.OrderedPair (96/3) (row 96 3) (row 97 3) :=
  stay_pair (by decide) root96 root97 (by decide +kernel)

theorem pair96Gap2 :
    RootTracking.OrderedPair (96/3) (row 96 3) (row 98 3) :=
  stay_pair (by decide) root96 root98 (by decide +kernel)

theorem pair96Gap3 :
    RootTracking.OrderedPair (96/3) (row 96 3) (row 99 3) :=
  rise_pair (by decide) root96 root99 (by decide +kernel)

theorem pair97Gap1 :
    RootTracking.OrderedPair (97/3) (row 97 3) (row 98 3) :=
  stay_pair (by decide) root97 root98 (by decide +kernel)

theorem pair97Gap2 :
    RootTracking.OrderedPair (97/3) (row 97 3) (row 99 3) :=
  rise_pair (by decide) root97 root99 (by decide +kernel)

theorem pair97Gap3 :
    RootTracking.OrderedPair (97/3) (row 97 3) (row 100 3) :=
  rise_pair (by decide) root97 root100 (by decide +kernel)

theorem pair98Gap1 :
    RootTracking.OrderedPair (98/3) (row 98 3) (row 99 3) :=
  rise_pair (by decide) root98 root99 (by decide +kernel)

theorem pair98Gap2 :
    RootTracking.OrderedPair (98/3) (row 98 3) (row 100 3) :=
  rise_pair (by decide) root98 root100 (by decide +kernel)

theorem pair98Gap3 :
    RootTracking.OrderedPair (98/3) (row 98 3) (row 101 3) :=
  rise_pair (by decide) root98 root101 (by decide +kernel)

theorem pair99Gap1 :
    RootTracking.OrderedPair (99/3) (row 99 3) (row 100 3) :=
  stay_pair (by decide) root99 root100 (by decide +kernel)

theorem pair99Gap2 :
    RootTracking.OrderedPair (99/3) (row 99 3) (row 101 3) :=
  stay_pair (by decide) root99 root101 (by decide +kernel)

theorem pair99Gap3 :
    RootTracking.OrderedPair (99/3) (row 99 3) (row 102 3) :=
  rise_pair (by decide) root99 root102 (by decide +kernel)

theorem pair100Gap1 :
    RootTracking.OrderedPair (100/3) (row 100 3) (row 101 3) :=
  stay_pair (by decide) root100 root101 (by decide +kernel)

theorem pair100Gap2 :
    RootTracking.OrderedPair (100/3) (row 100 3) (row 102 3) :=
  rise_pair (by decide) root100 root102 (by decide +kernel)

theorem pair100Gap3 :
    RootTracking.OrderedPair (100/3) (row 100 3) (row 103 3) :=
  rise_pair (by decide) root100 root103 (by decide +kernel)

theorem pair101Gap1 :
    RootTracking.OrderedPair (101/3) (row 101 3) (row 102 3) :=
  rise_pair (by decide) root101 root102 (by decide +kernel)

theorem pair101Gap2 :
    RootTracking.OrderedPair (101/3) (row 101 3) (row 103 3) :=
  rise_pair (by decide) root101 root103 (by decide +kernel)

theorem pair101Gap3 :
    RootTracking.OrderedPair (101/3) (row 101 3) (row 104 3) :=
  rise_pair (by decide) root101 root104 (by decide +kernel)

theorem pair102Gap1 :
    RootTracking.OrderedPair (102/3) (row 102 3) (row 103 3) :=
  stay_pair (by decide) root102 root103 (by decide +kernel)

theorem pair102Gap2 :
    RootTracking.OrderedPair (102/3) (row 102 3) (row 104 3) :=
  stay_pair (by decide) root102 root104 (by decide +kernel)

theorem pair102Gap3 :
    RootTracking.OrderedPair (102/3) (row 102 3) (row 105 3) :=
  rise_pair (by decide) root102 root105 (by decide +kernel)

theorem pair103Gap1 :
    RootTracking.OrderedPair (103/3) (row 103 3) (row 104 3) :=
  stay_pair (by decide) root103 root104 (by decide +kernel)

theorem pair103Gap2 :
    RootTracking.OrderedPair (103/3) (row 103 3) (row 105 3) :=
  rise_pair (by decide) root103 root105 (by decide +kernel)

theorem pair103Gap3 :
    RootTracking.OrderedPair (103/3) (row 103 3) (row 106 3) :=
  rise_pair (by decide) root103 root106 (by decide +kernel)

theorem range96Gap1 (n : ℕ) (lo : 96 ≤ n) (hi : n ≤ 103) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair96Gap1
  · exact pair97Gap1
  · exact pair98Gap1
  · exact pair99Gap1
  · exact pair100Gap1
  · exact pair101Gap1
  · exact pair102Gap1
  · exact pair103Gap1

theorem range96Gap2 (n : ℕ) (lo : 96 ≤ n) (hi : n ≤ 103) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair96Gap2
  · exact pair97Gap2
  · exact pair98Gap2
  · exact pair99Gap2
  · exact pair100Gap2
  · exact pair101Gap2
  · exact pair102Gap2
  · exact pair103Gap2

theorem range96Gap3 (n : ℕ) (lo : 96 ≤ n) (hi : n ≤ 103) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair96Gap3
  · exact pair97Gap3
  · exact pair98Gap3
  · exact pair99Gap3
  · exact pair100Gap3
  · exact pair101Gap3
  · exact pair102Gap3
  · exact pair103Gap3


#print axioms range96Gap1
#print axioms range96Gap2
#print axioms range96Gap3

end OrderedPartitions.ThreePoleFinite
