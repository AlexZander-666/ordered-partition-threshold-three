import OrderedPartitions.ThreePoleFiniteData.Roots064
import OrderedPartitions.ThreePoleFiniteData.Roots072

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair64Gap1 :
    RootTracking.OrderedPair (64/3) (row 64 3) (row 65 3) :=
  stay_pair (by decide) root64 root65 (by decide +kernel)

theorem pair64Gap2 :
    RootTracking.OrderedPair (64/3) (row 64 3) (row 66 3) :=
  rise_pair (by decide) root64 root66 (by decide +kernel)

theorem pair64Gap3 :
    RootTracking.OrderedPair (64/3) (row 64 3) (row 67 3) :=
  rise_pair (by decide) root64 root67 (by decide +kernel)

theorem pair65Gap1 :
    RootTracking.OrderedPair (65/3) (row 65 3) (row 66 3) :=
  rise_pair (by decide) root65 root66 (by decide +kernel)

theorem pair65Gap2 :
    RootTracking.OrderedPair (65/3) (row 65 3) (row 67 3) :=
  rise_pair (by decide) root65 root67 (by decide +kernel)

theorem pair65Gap3 :
    RootTracking.OrderedPair (65/3) (row 65 3) (row 68 3) :=
  rise_pair (by decide) root65 root68 (by decide +kernel)

theorem pair66Gap1 :
    RootTracking.OrderedPair (66/3) (row 66 3) (row 67 3) :=
  stay_pair (by decide) root66 root67 (by decide +kernel)

theorem pair66Gap2 :
    RootTracking.OrderedPair (66/3) (row 66 3) (row 68 3) :=
  stay_pair (by decide) root66 root68 (by decide +kernel)

theorem pair66Gap3 :
    RootTracking.OrderedPair (66/3) (row 66 3) (row 69 3) :=
  rise_pair (by decide) root66 root69 (by decide +kernel)

theorem pair67Gap1 :
    RootTracking.OrderedPair (67/3) (row 67 3) (row 68 3) :=
  stay_pair (by decide) root67 root68 (by decide +kernel)

theorem pair67Gap2 :
    RootTracking.OrderedPair (67/3) (row 67 3) (row 69 3) :=
  rise_pair (by decide) root67 root69 (by decide +kernel)

theorem pair67Gap3 :
    RootTracking.OrderedPair (67/3) (row 67 3) (row 70 3) :=
  rise_pair (by decide) root67 root70 (by decide +kernel)

theorem pair68Gap1 :
    RootTracking.OrderedPair (68/3) (row 68 3) (row 69 3) :=
  rise_pair (by decide) root68 root69 (by decide +kernel)

theorem pair68Gap2 :
    RootTracking.OrderedPair (68/3) (row 68 3) (row 70 3) :=
  rise_pair (by decide) root68 root70 (by decide +kernel)

theorem pair68Gap3 :
    RootTracking.OrderedPair (68/3) (row 68 3) (row 71 3) :=
  rise_pair (by decide) root68 root71 (by decide +kernel)

theorem pair69Gap1 :
    RootTracking.OrderedPair (69/3) (row 69 3) (row 70 3) :=
  stay_pair (by decide) root69 root70 (by decide +kernel)

theorem pair69Gap2 :
    RootTracking.OrderedPair (69/3) (row 69 3) (row 71 3) :=
  stay_pair (by decide) root69 root71 (by decide +kernel)

theorem pair69Gap3 :
    RootTracking.OrderedPair (69/3) (row 69 3) (row 72 3) :=
  rise_pair (by decide) root69 root72 (by decide +kernel)

theorem pair70Gap1 :
    RootTracking.OrderedPair (70/3) (row 70 3) (row 71 3) :=
  stay_pair (by decide) root70 root71 (by decide +kernel)

theorem pair70Gap2 :
    RootTracking.OrderedPair (70/3) (row 70 3) (row 72 3) :=
  rise_pair (by decide) root70 root72 (by decide +kernel)

theorem pair70Gap3 :
    RootTracking.OrderedPair (70/3) (row 70 3) (row 73 3) :=
  rise_pair (by decide) root70 root73 (by decide +kernel)

theorem pair71Gap1 :
    RootTracking.OrderedPair (71/3) (row 71 3) (row 72 3) :=
  rise_pair (by decide) root71 root72 (by decide +kernel)

theorem pair71Gap2 :
    RootTracking.OrderedPair (71/3) (row 71 3) (row 73 3) :=
  rise_pair (by decide) root71 root73 (by decide +kernel)

theorem pair71Gap3 :
    RootTracking.OrderedPair (71/3) (row 71 3) (row 74 3) :=
  rise_pair (by decide) root71 root74 (by decide +kernel)

theorem range64Gap1 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair64Gap1
  · exact pair65Gap1
  · exact pair66Gap1
  · exact pair67Gap1
  · exact pair68Gap1
  · exact pair69Gap1
  · exact pair70Gap1
  · exact pair71Gap1

theorem range64Gap2 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair64Gap2
  · exact pair65Gap2
  · exact pair66Gap2
  · exact pair67Gap2
  · exact pair68Gap2
  · exact pair69Gap2
  · exact pair70Gap2
  · exact pair71Gap2

theorem range64Gap3 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair64Gap3
  · exact pair65Gap3
  · exact pair66Gap3
  · exact pair67Gap3
  · exact pair68Gap3
  · exact pair69Gap3
  · exact pair70Gap3
  · exact pair71Gap3


#print axioms range64Gap1
#print axioms range64Gap2
#print axioms range64Gap3

end OrderedPartitions.ThreePoleFinite
