import OrderedPartitions.ThreePoleFiniteData.Roots208
import OrderedPartitions.ThreePoleFiniteData.Roots216

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair208Gap1 :
    RootTracking.OrderedPair (208/3) (row 208 3) (row 209 3) :=
  stay_pair (by decide) root208 root209 (by decide +kernel)

theorem pair208Gap2 :
    RootTracking.OrderedPair (208/3) (row 208 3) (row 210 3) :=
  rise_pair (by decide) root208 root210 (by decide +kernel)

theorem pair208Gap3 :
    RootTracking.OrderedPair (208/3) (row 208 3) (row 211 3) :=
  rise_pair (by decide) root208 root211 (by decide +kernel)

theorem pair209Gap1 :
    RootTracking.OrderedPair (209/3) (row 209 3) (row 210 3) :=
  rise_pair (by decide) root209 root210 (by decide +kernel)

theorem pair209Gap2 :
    RootTracking.OrderedPair (209/3) (row 209 3) (row 211 3) :=
  rise_pair (by decide) root209 root211 (by decide +kernel)

theorem pair209Gap3 :
    RootTracking.OrderedPair (209/3) (row 209 3) (row 212 3) :=
  rise_pair (by decide) root209 root212 (by decide +kernel)

theorem pair210Gap1 :
    RootTracking.OrderedPair (210/3) (row 210 3) (row 211 3) :=
  stay_pair (by decide) root210 root211 (by decide +kernel)

theorem pair210Gap2 :
    RootTracking.OrderedPair (210/3) (row 210 3) (row 212 3) :=
  stay_pair (by decide) root210 root212 (by decide +kernel)

theorem pair210Gap3 :
    RootTracking.OrderedPair (210/3) (row 210 3) (row 213 3) :=
  rise_pair (by decide) root210 root213 (by decide +kernel)

theorem pair211Gap1 :
    RootTracking.OrderedPair (211/3) (row 211 3) (row 212 3) :=
  stay_pair (by decide) root211 root212 (by decide +kernel)

theorem pair211Gap2 :
    RootTracking.OrderedPair (211/3) (row 211 3) (row 213 3) :=
  rise_pair (by decide) root211 root213 (by decide +kernel)

theorem pair211Gap3 :
    RootTracking.OrderedPair (211/3) (row 211 3) (row 214 3) :=
  rise_pair (by decide) root211 root214 (by decide +kernel)

theorem pair212Gap1 :
    RootTracking.OrderedPair (212/3) (row 212 3) (row 213 3) :=
  rise_pair (by decide) root212 root213 (by decide +kernel)

theorem pair212Gap2 :
    RootTracking.OrderedPair (212/3) (row 212 3) (row 214 3) :=
  rise_pair (by decide) root212 root214 (by decide +kernel)

theorem pair212Gap3 :
    RootTracking.OrderedPair (212/3) (row 212 3) (row 215 3) :=
  rise_pair (by decide) root212 root215 (by decide +kernel)

theorem pair213Gap1 :
    RootTracking.OrderedPair (213/3) (row 213 3) (row 214 3) :=
  stay_pair (by decide) root213 root214 (by decide +kernel)

theorem pair213Gap2 :
    RootTracking.OrderedPair (213/3) (row 213 3) (row 215 3) :=
  stay_pair (by decide) root213 root215 (by decide +kernel)

theorem pair213Gap3 :
    RootTracking.OrderedPair (213/3) (row 213 3) (row 216 3) :=
  rise_pair (by decide) root213 root216 (by decide +kernel)

theorem pair214Gap1 :
    RootTracking.OrderedPair (214/3) (row 214 3) (row 215 3) :=
  stay_pair (by decide) root214 root215 (by decide +kernel)

theorem pair214Gap2 :
    RootTracking.OrderedPair (214/3) (row 214 3) (row 216 3) :=
  rise_pair (by decide) root214 root216 (by decide +kernel)

theorem pair214Gap3 :
    RootTracking.OrderedPair (214/3) (row 214 3) (row 217 3) :=
  rise_pair (by decide) root214 root217 (by decide +kernel)

theorem pair215Gap1 :
    RootTracking.OrderedPair (215/3) (row 215 3) (row 216 3) :=
  rise_pair (by decide) root215 root216 (by decide +kernel)

theorem pair215Gap2 :
    RootTracking.OrderedPair (215/3) (row 215 3) (row 217 3) :=
  rise_pair (by decide) root215 root217 (by decide +kernel)

theorem pair215Gap3 :
    RootTracking.OrderedPair (215/3) (row 215 3) (row 218 3) :=
  rise_pair (by decide) root215 root218 (by decide +kernel)

theorem range208Gap1 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair208Gap1
  · exact pair209Gap1
  · exact pair210Gap1
  · exact pair211Gap1
  · exact pair212Gap1
  · exact pair213Gap1
  · exact pair214Gap1
  · exact pair215Gap1

theorem range208Gap2 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair208Gap2
  · exact pair209Gap2
  · exact pair210Gap2
  · exact pair211Gap2
  · exact pair212Gap2
  · exact pair213Gap2
  · exact pair214Gap2
  · exact pair215Gap2

theorem range208Gap3 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair208Gap3
  · exact pair209Gap3
  · exact pair210Gap3
  · exact pair211Gap3
  · exact pair212Gap3
  · exact pair213Gap3
  · exact pair214Gap3
  · exact pair215Gap3


#print axioms range208Gap1
#print axioms range208Gap2
#print axioms range208Gap3

end OrderedPartitions.ThreePoleFinite
