import OrderedPartitions.ThreePoleFiniteData.Roots032
import OrderedPartitions.ThreePoleFiniteData.Roots040

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair32Gap1 :
    RootTracking.OrderedPair (32/3) (row 32 3) (row 33 3) :=
  rise_pair (by decide) root32 root33 (by decide +kernel)

theorem pair32Gap2 :
    RootTracking.OrderedPair (32/3) (row 32 3) (row 34 3) :=
  rise_pair (by decide) root32 root34 (by decide +kernel)

theorem pair32Gap3 :
    RootTracking.OrderedPair (32/3) (row 32 3) (row 35 3) :=
  rise_pair (by decide) root32 root35 (by decide +kernel)

theorem pair33Gap1 :
    RootTracking.OrderedPair (33/3) (row 33 3) (row 34 3) :=
  stay_pair (by decide) root33 root34 (by decide +kernel)

theorem pair33Gap2 :
    RootTracking.OrderedPair (33/3) (row 33 3) (row 35 3) :=
  stay_pair (by decide) root33 root35 (by decide +kernel)

theorem pair33Gap3 :
    RootTracking.OrderedPair (33/3) (row 33 3) (row 36 3) :=
  rise_pair (by decide) root33 root36 (by decide +kernel)

theorem pair34Gap1 :
    RootTracking.OrderedPair (34/3) (row 34 3) (row 35 3) :=
  stay_pair (by decide) root34 root35 (by decide +kernel)

theorem pair34Gap2 :
    RootTracking.OrderedPair (34/3) (row 34 3) (row 36 3) :=
  rise_pair (by decide) root34 root36 (by decide +kernel)

theorem pair34Gap3 :
    RootTracking.OrderedPair (34/3) (row 34 3) (row 37 3) :=
  rise_pair (by decide) root34 root37 (by decide +kernel)

theorem pair35Gap1 :
    RootTracking.OrderedPair (35/3) (row 35 3) (row 36 3) :=
  rise_pair (by decide) root35 root36 (by decide +kernel)

theorem pair35Gap2 :
    RootTracking.OrderedPair (35/3) (row 35 3) (row 37 3) :=
  rise_pair (by decide) root35 root37 (by decide +kernel)

theorem pair35Gap3 :
    RootTracking.OrderedPair (35/3) (row 35 3) (row 38 3) :=
  rise_pair (by decide) root35 root38 (by decide +kernel)

theorem pair36Gap1 :
    RootTracking.OrderedPair (36/3) (row 36 3) (row 37 3) :=
  stay_pair (by decide) root36 root37 (by decide +kernel)

theorem pair36Gap2 :
    RootTracking.OrderedPair (36/3) (row 36 3) (row 38 3) :=
  stay_pair (by decide) root36 root38 (by decide +kernel)

theorem pair36Gap3 :
    RootTracking.OrderedPair (36/3) (row 36 3) (row 39 3) :=
  rise_pair (by decide) root36 root39 (by decide +kernel)

theorem pair37Gap1 :
    RootTracking.OrderedPair (37/3) (row 37 3) (row 38 3) :=
  stay_pair (by decide) root37 root38 (by decide +kernel)

theorem pair37Gap2 :
    RootTracking.OrderedPair (37/3) (row 37 3) (row 39 3) :=
  rise_pair (by decide) root37 root39 (by decide +kernel)

theorem pair37Gap3 :
    RootTracking.OrderedPair (37/3) (row 37 3) (row 40 3) :=
  rise_pair (by decide) root37 root40 (by decide +kernel)

theorem pair38Gap1 :
    RootTracking.OrderedPair (38/3) (row 38 3) (row 39 3) :=
  rise_pair (by decide) root38 root39 (by decide +kernel)

theorem pair38Gap2 :
    RootTracking.OrderedPair (38/3) (row 38 3) (row 40 3) :=
  rise_pair (by decide) root38 root40 (by decide +kernel)

theorem pair38Gap3 :
    RootTracking.OrderedPair (38/3) (row 38 3) (row 41 3) :=
  rise_pair (by decide) root38 root41 (by decide +kernel)

theorem pair39Gap1 :
    RootTracking.OrderedPair (39/3) (row 39 3) (row 40 3) :=
  stay_pair (by decide) root39 root40 (by decide +kernel)

theorem pair39Gap2 :
    RootTracking.OrderedPair (39/3) (row 39 3) (row 41 3) :=
  stay_pair (by decide) root39 root41 (by decide +kernel)

theorem pair39Gap3 :
    RootTracking.OrderedPair (39/3) (row 39 3) (row 42 3) :=
  rise_pair (by decide) root39 root42 (by decide +kernel)

theorem range32Gap1 (n : ℕ) (lo : 32 ≤ n) (hi : n ≤ 39) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair32Gap1
  · exact pair33Gap1
  · exact pair34Gap1
  · exact pair35Gap1
  · exact pair36Gap1
  · exact pair37Gap1
  · exact pair38Gap1
  · exact pair39Gap1

theorem range32Gap2 (n : ℕ) (lo : 32 ≤ n) (hi : n ≤ 39) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair32Gap2
  · exact pair33Gap2
  · exact pair34Gap2
  · exact pair35Gap2
  · exact pair36Gap2
  · exact pair37Gap2
  · exact pair38Gap2
  · exact pair39Gap2

theorem range32Gap3 (n : ℕ) (lo : 32 ≤ n) (hi : n ≤ 39) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair32Gap3
  · exact pair33Gap3
  · exact pair34Gap3
  · exact pair35Gap3
  · exact pair36Gap3
  · exact pair37Gap3
  · exact pair38Gap3
  · exact pair39Gap3


#print axioms range32Gap1
#print axioms range32Gap2
#print axioms range32Gap3

end OrderedPartitions.ThreePoleFinite
