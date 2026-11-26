import OrderedPartitions.ThreePoleFiniteData.Roots008
import OrderedPartitions.ThreePoleFiniteData.Roots016

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair8Gap1 :
    RootTracking.OrderedPair (8/3) (row 8 3) (row 9 3) :=
  rise_pair (by decide) root8 root9 (by decide +kernel)

theorem pair8Gap2 :
    RootTracking.OrderedPair (8/3) (row 8 3) (row 10 3) :=
  rise_pair (by decide) root8 root10 (by decide +kernel)

theorem pair8Gap3 :
    RootTracking.OrderedPair (8/3) (row 8 3) (row 11 3) :=
  rise_pair (by decide) root8 root11 (by decide +kernel)

theorem pair9Gap1 :
    RootTracking.OrderedPair (9/3) (row 9 3) (row 10 3) :=
  stay_pair (by decide) root9 root10 (by decide +kernel)

theorem pair9Gap2 :
    RootTracking.OrderedPair (9/3) (row 9 3) (row 11 3) :=
  stay_pair (by decide) root9 root11 (by decide +kernel)

theorem pair9Gap3 :
    RootTracking.OrderedPair (9/3) (row 9 3) (row 12 3) :=
  rise_pair (by decide) root9 root12 (by decide +kernel)

theorem pair10Gap1 :
    RootTracking.OrderedPair (10/3) (row 10 3) (row 11 3) :=
  stay_pair (by decide) root10 root11 (by decide +kernel)

theorem pair10Gap2 :
    RootTracking.OrderedPair (10/3) (row 10 3) (row 12 3) :=
  rise_pair (by decide) root10 root12 (by decide +kernel)

theorem pair10Gap3 :
    RootTracking.OrderedPair (10/3) (row 10 3) (row 13 3) :=
  rise_pair (by decide) root10 root13 (by decide +kernel)

theorem pair11Gap1 :
    RootTracking.OrderedPair (11/3) (row 11 3) (row 12 3) :=
  rise_pair (by decide) root11 root12 (by decide +kernel)

theorem pair11Gap2 :
    RootTracking.OrderedPair (11/3) (row 11 3) (row 13 3) :=
  rise_pair (by decide) root11 root13 (by decide +kernel)

theorem pair11Gap3 :
    RootTracking.OrderedPair (11/3) (row 11 3) (row 14 3) :=
  rise_pair (by decide) root11 root14 (by decide +kernel)

theorem pair12Gap1 :
    RootTracking.OrderedPair (12/3) (row 12 3) (row 13 3) :=
  stay_pair (by decide) root12 root13 (by decide +kernel)

theorem pair12Gap2 :
    RootTracking.OrderedPair (12/3) (row 12 3) (row 14 3) :=
  stay_pair (by decide) root12 root14 (by decide +kernel)

theorem pair12Gap3 :
    RootTracking.OrderedPair (12/3) (row 12 3) (row 15 3) :=
  rise_pair (by decide) root12 root15 (by decide +kernel)

theorem pair13Gap1 :
    RootTracking.OrderedPair (13/3) (row 13 3) (row 14 3) :=
  stay_pair (by decide) root13 root14 (by decide +kernel)

theorem pair13Gap2 :
    RootTracking.OrderedPair (13/3) (row 13 3) (row 15 3) :=
  rise_pair (by decide) root13 root15 (by decide +kernel)

theorem pair13Gap3 :
    RootTracking.OrderedPair (13/3) (row 13 3) (row 16 3) :=
  rise_pair (by decide) root13 root16 (by decide +kernel)

theorem pair14Gap1 :
    RootTracking.OrderedPair (14/3) (row 14 3) (row 15 3) :=
  rise_pair (by decide) root14 root15 (by decide +kernel)

theorem pair14Gap2 :
    RootTracking.OrderedPair (14/3) (row 14 3) (row 16 3) :=
  rise_pair (by decide) root14 root16 (by decide +kernel)

theorem pair14Gap3 :
    RootTracking.OrderedPair (14/3) (row 14 3) (row 17 3) :=
  rise_pair (by decide) root14 root17 (by decide +kernel)

theorem pair15Gap1 :
    RootTracking.OrderedPair (15/3) (row 15 3) (row 16 3) :=
  stay_pair (by decide) root15 root16 (by decide +kernel)

theorem pair15Gap2 :
    RootTracking.OrderedPair (15/3) (row 15 3) (row 17 3) :=
  stay_pair (by decide) root15 root17 (by decide +kernel)

theorem pair15Gap3 :
    RootTracking.OrderedPair (15/3) (row 15 3) (row 18 3) :=
  rise_pair (by decide) root15 root18 (by decide +kernel)

theorem range8Gap1 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair8Gap1
  · exact pair9Gap1
  · exact pair10Gap1
  · exact pair11Gap1
  · exact pair12Gap1
  · exact pair13Gap1
  · exact pair14Gap1
  · exact pair15Gap1

theorem range8Gap2 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair8Gap2
  · exact pair9Gap2
  · exact pair10Gap2
  · exact pair11Gap2
  · exact pair12Gap2
  · exact pair13Gap2
  · exact pair14Gap2
  · exact pair15Gap2

theorem range8Gap3 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair8Gap3
  · exact pair9Gap3
  · exact pair10Gap3
  · exact pair11Gap3
  · exact pair12Gap3
  · exact pair13Gap3
  · exact pair14Gap3
  · exact pair15Gap3


#print axioms range8Gap1
#print axioms range8Gap2
#print axioms range8Gap3

end OrderedPartitions.ThreePoleFinite
