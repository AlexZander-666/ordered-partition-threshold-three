import OrderedPartitions.ThreePoleFiniteData.Roots088
import OrderedPartitions.ThreePoleFiniteData.Roots096

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair88Gap1 :
    RootTracking.OrderedPair (88/3) (row 88 3) (row 89 3) :=
  stay_pair (by decide) root88 root89 (by decide +kernel)

theorem pair88Gap2 :
    RootTracking.OrderedPair (88/3) (row 88 3) (row 90 3) :=
  rise_pair (by decide) root88 root90 (by decide +kernel)

theorem pair88Gap3 :
    RootTracking.OrderedPair (88/3) (row 88 3) (row 91 3) :=
  rise_pair (by decide) root88 root91 (by decide +kernel)

theorem pair89Gap1 :
    RootTracking.OrderedPair (89/3) (row 89 3) (row 90 3) :=
  rise_pair (by decide) root89 root90 (by decide +kernel)

theorem pair89Gap2 :
    RootTracking.OrderedPair (89/3) (row 89 3) (row 91 3) :=
  rise_pair (by decide) root89 root91 (by decide +kernel)

theorem pair89Gap3 :
    RootTracking.OrderedPair (89/3) (row 89 3) (row 92 3) :=
  rise_pair (by decide) root89 root92 (by decide +kernel)

theorem pair90Gap1 :
    RootTracking.OrderedPair (90/3) (row 90 3) (row 91 3) :=
  stay_pair (by decide) root90 root91 (by decide +kernel)

theorem pair90Gap2 :
    RootTracking.OrderedPair (90/3) (row 90 3) (row 92 3) :=
  stay_pair (by decide) root90 root92 (by decide +kernel)

theorem pair90Gap3 :
    RootTracking.OrderedPair (90/3) (row 90 3) (row 93 3) :=
  rise_pair (by decide) root90 root93 (by decide +kernel)

theorem pair91Gap1 :
    RootTracking.OrderedPair (91/3) (row 91 3) (row 92 3) :=
  stay_pair (by decide) root91 root92 (by decide +kernel)

theorem pair91Gap2 :
    RootTracking.OrderedPair (91/3) (row 91 3) (row 93 3) :=
  rise_pair (by decide) root91 root93 (by decide +kernel)

theorem pair91Gap3 :
    RootTracking.OrderedPair (91/3) (row 91 3) (row 94 3) :=
  rise_pair (by decide) root91 root94 (by decide +kernel)

theorem pair92Gap1 :
    RootTracking.OrderedPair (92/3) (row 92 3) (row 93 3) :=
  rise_pair (by decide) root92 root93 (by decide +kernel)

theorem pair92Gap2 :
    RootTracking.OrderedPair (92/3) (row 92 3) (row 94 3) :=
  rise_pair (by decide) root92 root94 (by decide +kernel)

theorem pair92Gap3 :
    RootTracking.OrderedPair (92/3) (row 92 3) (row 95 3) :=
  rise_pair (by decide) root92 root95 (by decide +kernel)

theorem pair93Gap1 :
    RootTracking.OrderedPair (93/3) (row 93 3) (row 94 3) :=
  stay_pair (by decide) root93 root94 (by decide +kernel)

theorem pair93Gap2 :
    RootTracking.OrderedPair (93/3) (row 93 3) (row 95 3) :=
  stay_pair (by decide) root93 root95 (by decide +kernel)

theorem pair93Gap3 :
    RootTracking.OrderedPair (93/3) (row 93 3) (row 96 3) :=
  rise_pair (by decide) root93 root96 (by decide +kernel)

theorem pair94Gap1 :
    RootTracking.OrderedPair (94/3) (row 94 3) (row 95 3) :=
  stay_pair (by decide) root94 root95 (by decide +kernel)

theorem pair94Gap2 :
    RootTracking.OrderedPair (94/3) (row 94 3) (row 96 3) :=
  rise_pair (by decide) root94 root96 (by decide +kernel)

theorem pair94Gap3 :
    RootTracking.OrderedPair (94/3) (row 94 3) (row 97 3) :=
  rise_pair (by decide) root94 root97 (by decide +kernel)

theorem pair95Gap1 :
    RootTracking.OrderedPair (95/3) (row 95 3) (row 96 3) :=
  rise_pair (by decide) root95 root96 (by decide +kernel)

theorem pair95Gap2 :
    RootTracking.OrderedPair (95/3) (row 95 3) (row 97 3) :=
  rise_pair (by decide) root95 root97 (by decide +kernel)

theorem pair95Gap3 :
    RootTracking.OrderedPair (95/3) (row 95 3) (row 98 3) :=
  rise_pair (by decide) root95 root98 (by decide +kernel)

theorem range88Gap1 (n : ℕ) (lo : 88 ≤ n) (hi : n ≤ 95) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair88Gap1
  · exact pair89Gap1
  · exact pair90Gap1
  · exact pair91Gap1
  · exact pair92Gap1
  · exact pair93Gap1
  · exact pair94Gap1
  · exact pair95Gap1

theorem range88Gap2 (n : ℕ) (lo : 88 ≤ n) (hi : n ≤ 95) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair88Gap2
  · exact pair89Gap2
  · exact pair90Gap2
  · exact pair91Gap2
  · exact pair92Gap2
  · exact pair93Gap2
  · exact pair94Gap2
  · exact pair95Gap2

theorem range88Gap3 (n : ℕ) (lo : 88 ≤ n) (hi : n ≤ 95) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair88Gap3
  · exact pair89Gap3
  · exact pair90Gap3
  · exact pair91Gap3
  · exact pair92Gap3
  · exact pair93Gap3
  · exact pair94Gap3
  · exact pair95Gap3


#print axioms range88Gap1
#print axioms range88Gap2
#print axioms range88Gap3

end OrderedPartitions.ThreePoleFinite
