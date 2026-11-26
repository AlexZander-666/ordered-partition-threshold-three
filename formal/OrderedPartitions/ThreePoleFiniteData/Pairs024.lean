import OrderedPartitions.ThreePoleFiniteData.Roots024
import OrderedPartitions.ThreePoleFiniteData.Roots032

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair24Gap1 :
    RootTracking.OrderedPair (24/3) (row 24 3) (row 25 3) :=
  stay_pair (by decide) root24 root25 (by decide +kernel)

theorem pair24Gap2 :
    RootTracking.OrderedPair (24/3) (row 24 3) (row 26 3) :=
  stay_pair (by decide) root24 root26 (by decide +kernel)

theorem pair24Gap3 :
    RootTracking.OrderedPair (24/3) (row 24 3) (row 27 3) :=
  rise_pair (by decide) root24 root27 (by decide +kernel)

theorem pair25Gap1 :
    RootTracking.OrderedPair (25/3) (row 25 3) (row 26 3) :=
  stay_pair (by decide) root25 root26 (by decide +kernel)

theorem pair25Gap2 :
    RootTracking.OrderedPair (25/3) (row 25 3) (row 27 3) :=
  rise_pair (by decide) root25 root27 (by decide +kernel)

theorem pair25Gap3 :
    RootTracking.OrderedPair (25/3) (row 25 3) (row 28 3) :=
  rise_pair (by decide) root25 root28 (by decide +kernel)

theorem pair26Gap1 :
    RootTracking.OrderedPair (26/3) (row 26 3) (row 27 3) :=
  rise_pair (by decide) root26 root27 (by decide +kernel)

theorem pair26Gap2 :
    RootTracking.OrderedPair (26/3) (row 26 3) (row 28 3) :=
  rise_pair (by decide) root26 root28 (by decide +kernel)

theorem pair26Gap3 :
    RootTracking.OrderedPair (26/3) (row 26 3) (row 29 3) :=
  rise_pair (by decide) root26 root29 (by decide +kernel)

theorem pair27Gap1 :
    RootTracking.OrderedPair (27/3) (row 27 3) (row 28 3) :=
  stay_pair (by decide) root27 root28 (by decide +kernel)

theorem pair27Gap2 :
    RootTracking.OrderedPair (27/3) (row 27 3) (row 29 3) :=
  stay_pair (by decide) root27 root29 (by decide +kernel)

theorem pair27Gap3 :
    RootTracking.OrderedPair (27/3) (row 27 3) (row 30 3) :=
  rise_pair (by decide) root27 root30 (by decide +kernel)

theorem pair28Gap1 :
    RootTracking.OrderedPair (28/3) (row 28 3) (row 29 3) :=
  stay_pair (by decide) root28 root29 (by decide +kernel)

theorem pair28Gap2 :
    RootTracking.OrderedPair (28/3) (row 28 3) (row 30 3) :=
  rise_pair (by decide) root28 root30 (by decide +kernel)

theorem pair28Gap3 :
    RootTracking.OrderedPair (28/3) (row 28 3) (row 31 3) :=
  rise_pair (by decide) root28 root31 (by decide +kernel)

theorem pair29Gap1 :
    RootTracking.OrderedPair (29/3) (row 29 3) (row 30 3) :=
  rise_pair (by decide) root29 root30 (by decide +kernel)

theorem pair29Gap2 :
    RootTracking.OrderedPair (29/3) (row 29 3) (row 31 3) :=
  rise_pair (by decide) root29 root31 (by decide +kernel)

theorem pair29Gap3 :
    RootTracking.OrderedPair (29/3) (row 29 3) (row 32 3) :=
  rise_pair (by decide) root29 root32 (by decide +kernel)

theorem pair30Gap1 :
    RootTracking.OrderedPair (30/3) (row 30 3) (row 31 3) :=
  stay_pair (by decide) root30 root31 (by decide +kernel)

theorem pair30Gap2 :
    RootTracking.OrderedPair (30/3) (row 30 3) (row 32 3) :=
  stay_pair (by decide) root30 root32 (by decide +kernel)

theorem pair30Gap3 :
    RootTracking.OrderedPair (30/3) (row 30 3) (row 33 3) :=
  rise_pair (by decide) root30 root33 (by decide +kernel)

theorem pair31Gap1 :
    RootTracking.OrderedPair (31/3) (row 31 3) (row 32 3) :=
  stay_pair (by decide) root31 root32 (by decide +kernel)

theorem pair31Gap2 :
    RootTracking.OrderedPair (31/3) (row 31 3) (row 33 3) :=
  rise_pair (by decide) root31 root33 (by decide +kernel)

theorem pair31Gap3 :
    RootTracking.OrderedPair (31/3) (row 31 3) (row 34 3) :=
  rise_pair (by decide) root31 root34 (by decide +kernel)

theorem range24Gap1 (n : ℕ) (lo : 24 ≤ n) (hi : n ≤ 31) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair24Gap1
  · exact pair25Gap1
  · exact pair26Gap1
  · exact pair27Gap1
  · exact pair28Gap1
  · exact pair29Gap1
  · exact pair30Gap1
  · exact pair31Gap1

theorem range24Gap2 (n : ℕ) (lo : 24 ≤ n) (hi : n ≤ 31) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair24Gap2
  · exact pair25Gap2
  · exact pair26Gap2
  · exact pair27Gap2
  · exact pair28Gap2
  · exact pair29Gap2
  · exact pair30Gap2
  · exact pair31Gap2

theorem range24Gap3 (n : ℕ) (lo : 24 ≤ n) (hi : n ≤ 31) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair24Gap3
  · exact pair25Gap3
  · exact pair26Gap3
  · exact pair27Gap3
  · exact pair28Gap3
  · exact pair29Gap3
  · exact pair30Gap3
  · exact pair31Gap3


#print axioms range24Gap1
#print axioms range24Gap2
#print axioms range24Gap3

end OrderedPartitions.ThreePoleFinite
