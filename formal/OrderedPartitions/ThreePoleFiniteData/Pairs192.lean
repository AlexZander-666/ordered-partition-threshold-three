import OrderedPartitions.ThreePoleFiniteData.Roots192
import OrderedPartitions.ThreePoleFiniteData.Roots200

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair192Gap1 :
    RootTracking.OrderedPair (192/3) (row 192 3) (row 193 3) :=
  stay_pair (by decide) root192 root193 (by decide +kernel)

theorem pair192Gap2 :
    RootTracking.OrderedPair (192/3) (row 192 3) (row 194 3) :=
  stay_pair (by decide) root192 root194 (by decide +kernel)

theorem pair192Gap3 :
    RootTracking.OrderedPair (192/3) (row 192 3) (row 195 3) :=
  rise_pair (by decide) root192 root195 (by decide +kernel)

theorem pair193Gap1 :
    RootTracking.OrderedPair (193/3) (row 193 3) (row 194 3) :=
  stay_pair (by decide) root193 root194 (by decide +kernel)

theorem pair193Gap2 :
    RootTracking.OrderedPair (193/3) (row 193 3) (row 195 3) :=
  rise_pair (by decide) root193 root195 (by decide +kernel)

theorem pair193Gap3 :
    RootTracking.OrderedPair (193/3) (row 193 3) (row 196 3) :=
  rise_pair (by decide) root193 root196 (by decide +kernel)

theorem pair194Gap1 :
    RootTracking.OrderedPair (194/3) (row 194 3) (row 195 3) :=
  rise_pair (by decide) root194 root195 (by decide +kernel)

theorem pair194Gap2 :
    RootTracking.OrderedPair (194/3) (row 194 3) (row 196 3) :=
  rise_pair (by decide) root194 root196 (by decide +kernel)

theorem pair194Gap3 :
    RootTracking.OrderedPair (194/3) (row 194 3) (row 197 3) :=
  rise_pair (by decide) root194 root197 (by decide +kernel)

theorem pair195Gap1 :
    RootTracking.OrderedPair (195/3) (row 195 3) (row 196 3) :=
  stay_pair (by decide) root195 root196 (by decide +kernel)

theorem pair195Gap2 :
    RootTracking.OrderedPair (195/3) (row 195 3) (row 197 3) :=
  stay_pair (by decide) root195 root197 (by decide +kernel)

theorem pair195Gap3 :
    RootTracking.OrderedPair (195/3) (row 195 3) (row 198 3) :=
  rise_pair (by decide) root195 root198 (by decide +kernel)

theorem pair196Gap1 :
    RootTracking.OrderedPair (196/3) (row 196 3) (row 197 3) :=
  stay_pair (by decide) root196 root197 (by decide +kernel)

theorem pair196Gap2 :
    RootTracking.OrderedPair (196/3) (row 196 3) (row 198 3) :=
  rise_pair (by decide) root196 root198 (by decide +kernel)

theorem pair196Gap3 :
    RootTracking.OrderedPair (196/3) (row 196 3) (row 199 3) :=
  rise_pair (by decide) root196 root199 (by decide +kernel)

theorem pair197Gap1 :
    RootTracking.OrderedPair (197/3) (row 197 3) (row 198 3) :=
  rise_pair (by decide) root197 root198 (by decide +kernel)

theorem pair197Gap2 :
    RootTracking.OrderedPair (197/3) (row 197 3) (row 199 3) :=
  rise_pair (by decide) root197 root199 (by decide +kernel)

theorem pair197Gap3 :
    RootTracking.OrderedPair (197/3) (row 197 3) (row 200 3) :=
  rise_pair (by decide) root197 root200 (by decide +kernel)

theorem pair198Gap1 :
    RootTracking.OrderedPair (198/3) (row 198 3) (row 199 3) :=
  stay_pair (by decide) root198 root199 (by decide +kernel)

theorem pair198Gap2 :
    RootTracking.OrderedPair (198/3) (row 198 3) (row 200 3) :=
  stay_pair (by decide) root198 root200 (by decide +kernel)

theorem pair198Gap3 :
    RootTracking.OrderedPair (198/3) (row 198 3) (row 201 3) :=
  rise_pair (by decide) root198 root201 (by decide +kernel)

theorem pair199Gap1 :
    RootTracking.OrderedPair (199/3) (row 199 3) (row 200 3) :=
  stay_pair (by decide) root199 root200 (by decide +kernel)

theorem pair199Gap2 :
    RootTracking.OrderedPair (199/3) (row 199 3) (row 201 3) :=
  rise_pair (by decide) root199 root201 (by decide +kernel)

theorem pair199Gap3 :
    RootTracking.OrderedPair (199/3) (row 199 3) (row 202 3) :=
  rise_pair (by decide) root199 root202 (by decide +kernel)

theorem range192Gap1 (n : ℕ) (lo : 192 ≤ n) (hi : n ≤ 199) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair192Gap1
  · exact pair193Gap1
  · exact pair194Gap1
  · exact pair195Gap1
  · exact pair196Gap1
  · exact pair197Gap1
  · exact pair198Gap1
  · exact pair199Gap1

theorem range192Gap2 (n : ℕ) (lo : 192 ≤ n) (hi : n ≤ 199) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair192Gap2
  · exact pair193Gap2
  · exact pair194Gap2
  · exact pair195Gap2
  · exact pair196Gap2
  · exact pair197Gap2
  · exact pair198Gap2
  · exact pair199Gap2

theorem range192Gap3 (n : ℕ) (lo : 192 ≤ n) (hi : n ≤ 199) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair192Gap3
  · exact pair193Gap3
  · exact pair194Gap3
  · exact pair195Gap3
  · exact pair196Gap3
  · exact pair197Gap3
  · exact pair198Gap3
  · exact pair199Gap3


#print axioms range192Gap1
#print axioms range192Gap2
#print axioms range192Gap3

end OrderedPartitions.ThreePoleFinite
