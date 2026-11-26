import OrderedPartitions.ThreePoleFiniteData.Roots128
import OrderedPartitions.ThreePoleFiniteData.Roots136

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair128Gap1 :
    RootTracking.OrderedPair (128/3) (row 128 3) (row 129 3) :=
  rise_pair (by decide) root128 root129 (by decide +kernel)

theorem pair128Gap2 :
    RootTracking.OrderedPair (128/3) (row 128 3) (row 130 3) :=
  rise_pair (by decide) root128 root130 (by decide +kernel)

theorem pair128Gap3 :
    RootTracking.OrderedPair (128/3) (row 128 3) (row 131 3) :=
  rise_pair (by decide) root128 root131 (by decide +kernel)

theorem pair129Gap1 :
    RootTracking.OrderedPair (129/3) (row 129 3) (row 130 3) :=
  stay_pair (by decide) root129 root130 (by decide +kernel)

theorem pair129Gap2 :
    RootTracking.OrderedPair (129/3) (row 129 3) (row 131 3) :=
  stay_pair (by decide) root129 root131 (by decide +kernel)

theorem pair129Gap3 :
    RootTracking.OrderedPair (129/3) (row 129 3) (row 132 3) :=
  rise_pair (by decide) root129 root132 (by decide +kernel)

theorem pair130Gap1 :
    RootTracking.OrderedPair (130/3) (row 130 3) (row 131 3) :=
  stay_pair (by decide) root130 root131 (by decide +kernel)

theorem pair130Gap2 :
    RootTracking.OrderedPair (130/3) (row 130 3) (row 132 3) :=
  rise_pair (by decide) root130 root132 (by decide +kernel)

theorem pair130Gap3 :
    RootTracking.OrderedPair (130/3) (row 130 3) (row 133 3) :=
  rise_pair (by decide) root130 root133 (by decide +kernel)

theorem pair131Gap1 :
    RootTracking.OrderedPair (131/3) (row 131 3) (row 132 3) :=
  rise_pair (by decide) root131 root132 (by decide +kernel)

theorem pair131Gap2 :
    RootTracking.OrderedPair (131/3) (row 131 3) (row 133 3) :=
  rise_pair (by decide) root131 root133 (by decide +kernel)

theorem pair131Gap3 :
    RootTracking.OrderedPair (131/3) (row 131 3) (row 134 3) :=
  rise_pair (by decide) root131 root134 (by decide +kernel)

theorem pair132Gap1 :
    RootTracking.OrderedPair (132/3) (row 132 3) (row 133 3) :=
  stay_pair (by decide) root132 root133 (by decide +kernel)

theorem pair132Gap2 :
    RootTracking.OrderedPair (132/3) (row 132 3) (row 134 3) :=
  stay_pair (by decide) root132 root134 (by decide +kernel)

theorem pair132Gap3 :
    RootTracking.OrderedPair (132/3) (row 132 3) (row 135 3) :=
  rise_pair (by decide) root132 root135 (by decide +kernel)

theorem pair133Gap1 :
    RootTracking.OrderedPair (133/3) (row 133 3) (row 134 3) :=
  stay_pair (by decide) root133 root134 (by decide +kernel)

theorem pair133Gap2 :
    RootTracking.OrderedPair (133/3) (row 133 3) (row 135 3) :=
  rise_pair (by decide) root133 root135 (by decide +kernel)

theorem pair133Gap3 :
    RootTracking.OrderedPair (133/3) (row 133 3) (row 136 3) :=
  rise_pair (by decide) root133 root136 (by decide +kernel)

theorem pair134Gap1 :
    RootTracking.OrderedPair (134/3) (row 134 3) (row 135 3) :=
  rise_pair (by decide) root134 root135 (by decide +kernel)

theorem pair134Gap2 :
    RootTracking.OrderedPair (134/3) (row 134 3) (row 136 3) :=
  rise_pair (by decide) root134 root136 (by decide +kernel)

theorem pair134Gap3 :
    RootTracking.OrderedPair (134/3) (row 134 3) (row 137 3) :=
  rise_pair (by decide) root134 root137 (by decide +kernel)

theorem pair135Gap1 :
    RootTracking.OrderedPair (135/3) (row 135 3) (row 136 3) :=
  stay_pair (by decide) root135 root136 (by decide +kernel)

theorem pair135Gap2 :
    RootTracking.OrderedPair (135/3) (row 135 3) (row 137 3) :=
  stay_pair (by decide) root135 root137 (by decide +kernel)

theorem pair135Gap3 :
    RootTracking.OrderedPair (135/3) (row 135 3) (row 138 3) :=
  rise_pair (by decide) root135 root138 (by decide +kernel)

theorem range128Gap1 (n : ℕ) (lo : 128 ≤ n) (hi : n ≤ 135) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair128Gap1
  · exact pair129Gap1
  · exact pair130Gap1
  · exact pair131Gap1
  · exact pair132Gap1
  · exact pair133Gap1
  · exact pair134Gap1
  · exact pair135Gap1

theorem range128Gap2 (n : ℕ) (lo : 128 ≤ n) (hi : n ≤ 135) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair128Gap2
  · exact pair129Gap2
  · exact pair130Gap2
  · exact pair131Gap2
  · exact pair132Gap2
  · exact pair133Gap2
  · exact pair134Gap2
  · exact pair135Gap2

theorem range128Gap3 (n : ℕ) (lo : 128 ≤ n) (hi : n ≤ 135) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair128Gap3
  · exact pair129Gap3
  · exact pair130Gap3
  · exact pair131Gap3
  · exact pair132Gap3
  · exact pair133Gap3
  · exact pair134Gap3
  · exact pair135Gap3


#print axioms range128Gap1
#print axioms range128Gap2
#print axioms range128Gap3

end OrderedPartitions.ThreePoleFinite
