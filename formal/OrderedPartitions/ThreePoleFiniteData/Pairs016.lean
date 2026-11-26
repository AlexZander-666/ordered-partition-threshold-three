import OrderedPartitions.ThreePoleFiniteData.Roots016
import OrderedPartitions.ThreePoleFiniteData.Roots024

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair16Gap1 :
    RootTracking.OrderedPair (16/3) (row 16 3) (row 17 3) :=
  stay_pair (by decide) root16 root17 (by decide +kernel)

theorem pair16Gap2 :
    RootTracking.OrderedPair (16/3) (row 16 3) (row 18 3) :=
  rise_pair (by decide) root16 root18 (by decide +kernel)

theorem pair16Gap3 :
    RootTracking.OrderedPair (16/3) (row 16 3) (row 19 3) :=
  rise_pair (by decide) root16 root19 (by decide +kernel)

theorem pair17Gap1 :
    RootTracking.OrderedPair (17/3) (row 17 3) (row 18 3) :=
  rise_pair (by decide) root17 root18 (by decide +kernel)

theorem pair17Gap2 :
    RootTracking.OrderedPair (17/3) (row 17 3) (row 19 3) :=
  rise_pair (by decide) root17 root19 (by decide +kernel)

theorem pair17Gap3 :
    RootTracking.OrderedPair (17/3) (row 17 3) (row 20 3) :=
  rise_pair (by decide) root17 root20 (by decide +kernel)

theorem pair18Gap1 :
    RootTracking.OrderedPair (18/3) (row 18 3) (row 19 3) :=
  stay_pair (by decide) root18 root19 (by decide +kernel)

theorem pair18Gap2 :
    RootTracking.OrderedPair (18/3) (row 18 3) (row 20 3) :=
  stay_pair (by decide) root18 root20 (by decide +kernel)

theorem pair18Gap3 :
    RootTracking.OrderedPair (18/3) (row 18 3) (row 21 3) :=
  rise_pair (by decide) root18 root21 (by decide +kernel)

theorem pair19Gap1 :
    RootTracking.OrderedPair (19/3) (row 19 3) (row 20 3) :=
  stay_pair (by decide) root19 root20 (by decide +kernel)

theorem pair19Gap2 :
    RootTracking.OrderedPair (19/3) (row 19 3) (row 21 3) :=
  rise_pair (by decide) root19 root21 (by decide +kernel)

theorem pair19Gap3 :
    RootTracking.OrderedPair (19/3) (row 19 3) (row 22 3) :=
  rise_pair (by decide) root19 root22 (by decide +kernel)

theorem pair20Gap1 :
    RootTracking.OrderedPair (20/3) (row 20 3) (row 21 3) :=
  rise_pair (by decide) root20 root21 (by decide +kernel)

theorem pair20Gap2 :
    RootTracking.OrderedPair (20/3) (row 20 3) (row 22 3) :=
  rise_pair (by decide) root20 root22 (by decide +kernel)

theorem pair20Gap3 :
    RootTracking.OrderedPair (20/3) (row 20 3) (row 23 3) :=
  rise_pair (by decide) root20 root23 (by decide +kernel)

theorem pair21Gap1 :
    RootTracking.OrderedPair (21/3) (row 21 3) (row 22 3) :=
  stay_pair (by decide) root21 root22 (by decide +kernel)

theorem pair21Gap2 :
    RootTracking.OrderedPair (21/3) (row 21 3) (row 23 3) :=
  stay_pair (by decide) root21 root23 (by decide +kernel)

theorem pair21Gap3 :
    RootTracking.OrderedPair (21/3) (row 21 3) (row 24 3) :=
  rise_pair (by decide) root21 root24 (by decide +kernel)

theorem pair22Gap1 :
    RootTracking.OrderedPair (22/3) (row 22 3) (row 23 3) :=
  stay_pair (by decide) root22 root23 (by decide +kernel)

theorem pair22Gap2 :
    RootTracking.OrderedPair (22/3) (row 22 3) (row 24 3) :=
  rise_pair (by decide) root22 root24 (by decide +kernel)

theorem pair22Gap3 :
    RootTracking.OrderedPair (22/3) (row 22 3) (row 25 3) :=
  rise_pair (by decide) root22 root25 (by decide +kernel)

theorem pair23Gap1 :
    RootTracking.OrderedPair (23/3) (row 23 3) (row 24 3) :=
  rise_pair (by decide) root23 root24 (by decide +kernel)

theorem pair23Gap2 :
    RootTracking.OrderedPair (23/3) (row 23 3) (row 25 3) :=
  rise_pair (by decide) root23 root25 (by decide +kernel)

theorem pair23Gap3 :
    RootTracking.OrderedPair (23/3) (row 23 3) (row 26 3) :=
  rise_pair (by decide) root23 root26 (by decide +kernel)

theorem range16Gap1 (n : ℕ) (lo : 16 ≤ n) (hi : n ≤ 23) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair16Gap1
  · exact pair17Gap1
  · exact pair18Gap1
  · exact pair19Gap1
  · exact pair20Gap1
  · exact pair21Gap1
  · exact pair22Gap1
  · exact pair23Gap1

theorem range16Gap2 (n : ℕ) (lo : 16 ≤ n) (hi : n ≤ 23) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair16Gap2
  · exact pair17Gap2
  · exact pair18Gap2
  · exact pair19Gap2
  · exact pair20Gap2
  · exact pair21Gap2
  · exact pair22Gap2
  · exact pair23Gap2

theorem range16Gap3 (n : ℕ) (lo : 16 ≤ n) (hi : n ≤ 23) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair16Gap3
  · exact pair17Gap3
  · exact pair18Gap3
  · exact pair19Gap3
  · exact pair20Gap3
  · exact pair21Gap3
  · exact pair22Gap3
  · exact pair23Gap3


#print axioms range16Gap1
#print axioms range16Gap2
#print axioms range16Gap3

end OrderedPartitions.ThreePoleFinite
