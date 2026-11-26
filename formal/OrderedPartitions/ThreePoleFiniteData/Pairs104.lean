import OrderedPartitions.ThreePoleFiniteData.Roots104
import OrderedPartitions.ThreePoleFiniteData.Roots112

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair104Gap1 :
    RootTracking.OrderedPair (104/3) (row 104 3) (row 105 3) :=
  rise_pair (by decide) root104 root105 (by decide +kernel)

theorem pair104Gap2 :
    RootTracking.OrderedPair (104/3) (row 104 3) (row 106 3) :=
  rise_pair (by decide) root104 root106 (by decide +kernel)

theorem pair104Gap3 :
    RootTracking.OrderedPair (104/3) (row 104 3) (row 107 3) :=
  rise_pair (by decide) root104 root107 (by decide +kernel)

theorem pair105Gap1 :
    RootTracking.OrderedPair (105/3) (row 105 3) (row 106 3) :=
  stay_pair (by decide) root105 root106 (by decide +kernel)

theorem pair105Gap2 :
    RootTracking.OrderedPair (105/3) (row 105 3) (row 107 3) :=
  stay_pair (by decide) root105 root107 (by decide +kernel)

theorem pair105Gap3 :
    RootTracking.OrderedPair (105/3) (row 105 3) (row 108 3) :=
  rise_pair (by decide) root105 root108 (by decide +kernel)

theorem pair106Gap1 :
    RootTracking.OrderedPair (106/3) (row 106 3) (row 107 3) :=
  stay_pair (by decide) root106 root107 (by decide +kernel)

theorem pair106Gap2 :
    RootTracking.OrderedPair (106/3) (row 106 3) (row 108 3) :=
  rise_pair (by decide) root106 root108 (by decide +kernel)

theorem pair106Gap3 :
    RootTracking.OrderedPair (106/3) (row 106 3) (row 109 3) :=
  rise_pair (by decide) root106 root109 (by decide +kernel)

theorem pair107Gap1 :
    RootTracking.OrderedPair (107/3) (row 107 3) (row 108 3) :=
  rise_pair (by decide) root107 root108 (by decide +kernel)

theorem pair107Gap2 :
    RootTracking.OrderedPair (107/3) (row 107 3) (row 109 3) :=
  rise_pair (by decide) root107 root109 (by decide +kernel)

theorem pair107Gap3 :
    RootTracking.OrderedPair (107/3) (row 107 3) (row 110 3) :=
  rise_pair (by decide) root107 root110 (by decide +kernel)

theorem pair108Gap1 :
    RootTracking.OrderedPair (108/3) (row 108 3) (row 109 3) :=
  stay_pair (by decide) root108 root109 (by decide +kernel)

theorem pair108Gap2 :
    RootTracking.OrderedPair (108/3) (row 108 3) (row 110 3) :=
  stay_pair (by decide) root108 root110 (by decide +kernel)

theorem pair108Gap3 :
    RootTracking.OrderedPair (108/3) (row 108 3) (row 111 3) :=
  rise_pair (by decide) root108 root111 (by decide +kernel)

theorem pair109Gap1 :
    RootTracking.OrderedPair (109/3) (row 109 3) (row 110 3) :=
  stay_pair (by decide) root109 root110 (by decide +kernel)

theorem pair109Gap2 :
    RootTracking.OrderedPair (109/3) (row 109 3) (row 111 3) :=
  rise_pair (by decide) root109 root111 (by decide +kernel)

theorem pair109Gap3 :
    RootTracking.OrderedPair (109/3) (row 109 3) (row 112 3) :=
  rise_pair (by decide) root109 root112 (by decide +kernel)

theorem pair110Gap1 :
    RootTracking.OrderedPair (110/3) (row 110 3) (row 111 3) :=
  rise_pair (by decide) root110 root111 (by decide +kernel)

theorem pair110Gap2 :
    RootTracking.OrderedPair (110/3) (row 110 3) (row 112 3) :=
  rise_pair (by decide) root110 root112 (by decide +kernel)

theorem pair110Gap3 :
    RootTracking.OrderedPair (110/3) (row 110 3) (row 113 3) :=
  rise_pair (by decide) root110 root113 (by decide +kernel)

theorem pair111Gap1 :
    RootTracking.OrderedPair (111/3) (row 111 3) (row 112 3) :=
  stay_pair (by decide) root111 root112 (by decide +kernel)

theorem pair111Gap2 :
    RootTracking.OrderedPair (111/3) (row 111 3) (row 113 3) :=
  stay_pair (by decide) root111 root113 (by decide +kernel)

theorem pair111Gap3 :
    RootTracking.OrderedPair (111/3) (row 111 3) (row 114 3) :=
  rise_pair (by decide) root111 root114 (by decide +kernel)

theorem range104Gap1 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair104Gap1
  · exact pair105Gap1
  · exact pair106Gap1
  · exact pair107Gap1
  · exact pair108Gap1
  · exact pair109Gap1
  · exact pair110Gap1
  · exact pair111Gap1

theorem range104Gap2 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair104Gap2
  · exact pair105Gap2
  · exact pair106Gap2
  · exact pair107Gap2
  · exact pair108Gap2
  · exact pair109Gap2
  · exact pair110Gap2
  · exact pair111Gap2

theorem range104Gap3 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair104Gap3
  · exact pair105Gap3
  · exact pair106Gap3
  · exact pair107Gap3
  · exact pair108Gap3
  · exact pair109Gap3
  · exact pair110Gap3
  · exact pair111Gap3


#print axioms range104Gap1
#print axioms range104Gap2
#print axioms range104Gap3

end OrderedPartitions.ThreePoleFinite
