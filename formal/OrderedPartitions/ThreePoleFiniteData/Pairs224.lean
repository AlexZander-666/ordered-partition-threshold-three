import OrderedPartitions.ThreePoleFiniteData.Roots224
import OrderedPartitions.ThreePoleFiniteData.Roots232

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair224Gap1 :
    RootTracking.OrderedPair (224/3) (row 224 3) (row 225 3) :=
  rise_pair (by decide) root224 root225 (by decide +kernel)

theorem pair224Gap2 :
    RootTracking.OrderedPair (224/3) (row 224 3) (row 226 3) :=
  rise_pair (by decide) root224 root226 (by decide +kernel)

theorem pair224Gap3 :
    RootTracking.OrderedPair (224/3) (row 224 3) (row 227 3) :=
  rise_pair (by decide) root224 root227 (by decide +kernel)

theorem pair225Gap1 :
    RootTracking.OrderedPair (225/3) (row 225 3) (row 226 3) :=
  stay_pair (by decide) root225 root226 (by decide +kernel)

theorem pair225Gap2 :
    RootTracking.OrderedPair (225/3) (row 225 3) (row 227 3) :=
  stay_pair (by decide) root225 root227 (by decide +kernel)

theorem pair225Gap3 :
    RootTracking.OrderedPair (225/3) (row 225 3) (row 228 3) :=
  rise_pair (by decide) root225 root228 (by decide +kernel)

theorem pair226Gap1 :
    RootTracking.OrderedPair (226/3) (row 226 3) (row 227 3) :=
  stay_pair (by decide) root226 root227 (by decide +kernel)

theorem pair226Gap2 :
    RootTracking.OrderedPair (226/3) (row 226 3) (row 228 3) :=
  rise_pair (by decide) root226 root228 (by decide +kernel)

theorem pair226Gap3 :
    RootTracking.OrderedPair (226/3) (row 226 3) (row 229 3) :=
  rise_pair (by decide) root226 root229 (by decide +kernel)

theorem pair227Gap1 :
    RootTracking.OrderedPair (227/3) (row 227 3) (row 228 3) :=
  rise_pair (by decide) root227 root228 (by decide +kernel)

theorem pair227Gap2 :
    RootTracking.OrderedPair (227/3) (row 227 3) (row 229 3) :=
  rise_pair (by decide) root227 root229 (by decide +kernel)

theorem pair227Gap3 :
    RootTracking.OrderedPair (227/3) (row 227 3) (row 230 3) :=
  rise_pair (by decide) root227 root230 (by decide +kernel)

theorem pair228Gap1 :
    RootTracking.OrderedPair (228/3) (row 228 3) (row 229 3) :=
  stay_pair (by decide) root228 root229 (by decide +kernel)

theorem pair228Gap2 :
    RootTracking.OrderedPair (228/3) (row 228 3) (row 230 3) :=
  stay_pair (by decide) root228 root230 (by decide +kernel)

theorem pair228Gap3 :
    RootTracking.OrderedPair (228/3) (row 228 3) (row 231 3) :=
  rise_pair (by decide) root228 root231 (by decide +kernel)

theorem pair229Gap1 :
    RootTracking.OrderedPair (229/3) (row 229 3) (row 230 3) :=
  stay_pair (by decide) root229 root230 (by decide +kernel)

theorem pair229Gap2 :
    RootTracking.OrderedPair (229/3) (row 229 3) (row 231 3) :=
  rise_pair (by decide) root229 root231 (by decide +kernel)

theorem pair229Gap3 :
    RootTracking.OrderedPair (229/3) (row 229 3) (row 232 3) :=
  rise_pair (by decide) root229 root232 (by decide +kernel)

theorem pair230Gap1 :
    RootTracking.OrderedPair (230/3) (row 230 3) (row 231 3) :=
  rise_pair (by decide) root230 root231 (by decide +kernel)

theorem pair230Gap2 :
    RootTracking.OrderedPair (230/3) (row 230 3) (row 232 3) :=
  rise_pair (by decide) root230 root232 (by decide +kernel)

theorem pair230Gap3 :
    RootTracking.OrderedPair (230/3) (row 230 3) (row 233 3) :=
  rise_pair (by decide) root230 root233 (by decide +kernel)

theorem pair231Gap1 :
    RootTracking.OrderedPair (231/3) (row 231 3) (row 232 3) :=
  stay_pair (by decide) root231 root232 (by decide +kernel)

theorem pair231Gap2 :
    RootTracking.OrderedPair (231/3) (row 231 3) (row 233 3) :=
  stay_pair (by decide) root231 root233 (by decide +kernel)

theorem pair231Gap3 :
    RootTracking.OrderedPair (231/3) (row 231 3) (row 234 3) :=
  rise_pair (by decide) root231 root234 (by decide +kernel)

theorem range224Gap1 (n : ℕ) (lo : 224 ≤ n) (hi : n ≤ 231) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair224Gap1
  · exact pair225Gap1
  · exact pair226Gap1
  · exact pair227Gap1
  · exact pair228Gap1
  · exact pair229Gap1
  · exact pair230Gap1
  · exact pair231Gap1

theorem range224Gap2 (n : ℕ) (lo : 224 ≤ n) (hi : n ≤ 231) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair224Gap2
  · exact pair225Gap2
  · exact pair226Gap2
  · exact pair227Gap2
  · exact pair228Gap2
  · exact pair229Gap2
  · exact pair230Gap2
  · exact pair231Gap2

theorem range224Gap3 (n : ℕ) (lo : 224 ≤ n) (hi : n ≤ 231) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair224Gap3
  · exact pair225Gap3
  · exact pair226Gap3
  · exact pair227Gap3
  · exact pair228Gap3
  · exact pair229Gap3
  · exact pair230Gap3
  · exact pair231Gap3


#print axioms range224Gap1
#print axioms range224Gap2
#print axioms range224Gap3

end OrderedPartitions.ThreePoleFinite
