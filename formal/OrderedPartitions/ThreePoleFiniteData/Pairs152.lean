import OrderedPartitions.ThreePoleFiniteData.Roots152
import OrderedPartitions.ThreePoleFiniteData.Roots160

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair152Gap1 :
    RootTracking.OrderedPair (152/3) (row 152 3) (row 153 3) :=
  rise_pair (by decide) root152 root153 (by decide +kernel)

theorem pair152Gap2 :
    RootTracking.OrderedPair (152/3) (row 152 3) (row 154 3) :=
  rise_pair (by decide) root152 root154 (by decide +kernel)

theorem pair152Gap3 :
    RootTracking.OrderedPair (152/3) (row 152 3) (row 155 3) :=
  rise_pair (by decide) root152 root155 (by decide +kernel)

theorem pair153Gap1 :
    RootTracking.OrderedPair (153/3) (row 153 3) (row 154 3) :=
  stay_pair (by decide) root153 root154 (by decide +kernel)

theorem pair153Gap2 :
    RootTracking.OrderedPair (153/3) (row 153 3) (row 155 3) :=
  stay_pair (by decide) root153 root155 (by decide +kernel)

theorem pair153Gap3 :
    RootTracking.OrderedPair (153/3) (row 153 3) (row 156 3) :=
  rise_pair (by decide) root153 root156 (by decide +kernel)

theorem pair154Gap1 :
    RootTracking.OrderedPair (154/3) (row 154 3) (row 155 3) :=
  stay_pair (by decide) root154 root155 (by decide +kernel)

theorem pair154Gap2 :
    RootTracking.OrderedPair (154/3) (row 154 3) (row 156 3) :=
  rise_pair (by decide) root154 root156 (by decide +kernel)

theorem pair154Gap3 :
    RootTracking.OrderedPair (154/3) (row 154 3) (row 157 3) :=
  rise_pair (by decide) root154 root157 (by decide +kernel)

theorem pair155Gap1 :
    RootTracking.OrderedPair (155/3) (row 155 3) (row 156 3) :=
  rise_pair (by decide) root155 root156 (by decide +kernel)

theorem pair155Gap2 :
    RootTracking.OrderedPair (155/3) (row 155 3) (row 157 3) :=
  rise_pair (by decide) root155 root157 (by decide +kernel)

theorem pair155Gap3 :
    RootTracking.OrderedPair (155/3) (row 155 3) (row 158 3) :=
  rise_pair (by decide) root155 root158 (by decide +kernel)

theorem pair156Gap1 :
    RootTracking.OrderedPair (156/3) (row 156 3) (row 157 3) :=
  stay_pair (by decide) root156 root157 (by decide +kernel)

theorem pair156Gap2 :
    RootTracking.OrderedPair (156/3) (row 156 3) (row 158 3) :=
  stay_pair (by decide) root156 root158 (by decide +kernel)

theorem pair156Gap3 :
    RootTracking.OrderedPair (156/3) (row 156 3) (row 159 3) :=
  rise_pair (by decide) root156 root159 (by decide +kernel)

theorem pair157Gap1 :
    RootTracking.OrderedPair (157/3) (row 157 3) (row 158 3) :=
  stay_pair (by decide) root157 root158 (by decide +kernel)

theorem pair157Gap2 :
    RootTracking.OrderedPair (157/3) (row 157 3) (row 159 3) :=
  rise_pair (by decide) root157 root159 (by decide +kernel)

theorem pair157Gap3 :
    RootTracking.OrderedPair (157/3) (row 157 3) (row 160 3) :=
  rise_pair (by decide) root157 root160 (by decide +kernel)

theorem pair158Gap1 :
    RootTracking.OrderedPair (158/3) (row 158 3) (row 159 3) :=
  rise_pair (by decide) root158 root159 (by decide +kernel)

theorem pair158Gap2 :
    RootTracking.OrderedPair (158/3) (row 158 3) (row 160 3) :=
  rise_pair (by decide) root158 root160 (by decide +kernel)

theorem pair158Gap3 :
    RootTracking.OrderedPair (158/3) (row 158 3) (row 161 3) :=
  rise_pair (by decide) root158 root161 (by decide +kernel)

theorem pair159Gap1 :
    RootTracking.OrderedPair (159/3) (row 159 3) (row 160 3) :=
  stay_pair (by decide) root159 root160 (by decide +kernel)

theorem pair159Gap2 :
    RootTracking.OrderedPair (159/3) (row 159 3) (row 161 3) :=
  stay_pair (by decide) root159 root161 (by decide +kernel)

theorem pair159Gap3 :
    RootTracking.OrderedPair (159/3) (row 159 3) (row 162 3) :=
  rise_pair (by decide) root159 root162 (by decide +kernel)

theorem range152Gap1 (n : ℕ) (lo : 152 ≤ n) (hi : n ≤ 159) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair152Gap1
  · exact pair153Gap1
  · exact pair154Gap1
  · exact pair155Gap1
  · exact pair156Gap1
  · exact pair157Gap1
  · exact pair158Gap1
  · exact pair159Gap1

theorem range152Gap2 (n : ℕ) (lo : 152 ≤ n) (hi : n ≤ 159) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair152Gap2
  · exact pair153Gap2
  · exact pair154Gap2
  · exact pair155Gap2
  · exact pair156Gap2
  · exact pair157Gap2
  · exact pair158Gap2
  · exact pair159Gap2

theorem range152Gap3 (n : ℕ) (lo : 152 ≤ n) (hi : n ≤ 159) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair152Gap3
  · exact pair153Gap3
  · exact pair154Gap3
  · exact pair155Gap3
  · exact pair156Gap3
  · exact pair157Gap3
  · exact pair158Gap3
  · exact pair159Gap3


#print axioms range152Gap1
#print axioms range152Gap2
#print axioms range152Gap3

end OrderedPartitions.ThreePoleFinite
