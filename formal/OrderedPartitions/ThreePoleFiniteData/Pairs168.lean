import OrderedPartitions.ThreePoleFiniteData.Roots168
import OrderedPartitions.ThreePoleFiniteData.Roots176

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair168Gap1 :
    RootTracking.OrderedPair (168/3) (row 168 3) (row 169 3) :=
  stay_pair (by decide) root168 root169 (by decide +kernel)

theorem pair168Gap2 :
    RootTracking.OrderedPair (168/3) (row 168 3) (row 170 3) :=
  stay_pair (by decide) root168 root170 (by decide +kernel)

theorem pair168Gap3 :
    RootTracking.OrderedPair (168/3) (row 168 3) (row 171 3) :=
  rise_pair (by decide) root168 root171 (by decide +kernel)

theorem pair169Gap1 :
    RootTracking.OrderedPair (169/3) (row 169 3) (row 170 3) :=
  stay_pair (by decide) root169 root170 (by decide +kernel)

theorem pair169Gap2 :
    RootTracking.OrderedPair (169/3) (row 169 3) (row 171 3) :=
  rise_pair (by decide) root169 root171 (by decide +kernel)

theorem pair169Gap3 :
    RootTracking.OrderedPair (169/3) (row 169 3) (row 172 3) :=
  rise_pair (by decide) root169 root172 (by decide +kernel)

theorem pair170Gap1 :
    RootTracking.OrderedPair (170/3) (row 170 3) (row 171 3) :=
  rise_pair (by decide) root170 root171 (by decide +kernel)

theorem pair170Gap2 :
    RootTracking.OrderedPair (170/3) (row 170 3) (row 172 3) :=
  rise_pair (by decide) root170 root172 (by decide +kernel)

theorem pair170Gap3 :
    RootTracking.OrderedPair (170/3) (row 170 3) (row 173 3) :=
  rise_pair (by decide) root170 root173 (by decide +kernel)

theorem pair171Gap1 :
    RootTracking.OrderedPair (171/3) (row 171 3) (row 172 3) :=
  stay_pair (by decide) root171 root172 (by decide +kernel)

theorem pair171Gap2 :
    RootTracking.OrderedPair (171/3) (row 171 3) (row 173 3) :=
  stay_pair (by decide) root171 root173 (by decide +kernel)

theorem pair171Gap3 :
    RootTracking.OrderedPair (171/3) (row 171 3) (row 174 3) :=
  rise_pair (by decide) root171 root174 (by decide +kernel)

theorem pair172Gap1 :
    RootTracking.OrderedPair (172/3) (row 172 3) (row 173 3) :=
  stay_pair (by decide) root172 root173 (by decide +kernel)

theorem pair172Gap2 :
    RootTracking.OrderedPair (172/3) (row 172 3) (row 174 3) :=
  rise_pair (by decide) root172 root174 (by decide +kernel)

theorem pair172Gap3 :
    RootTracking.OrderedPair (172/3) (row 172 3) (row 175 3) :=
  rise_pair (by decide) root172 root175 (by decide +kernel)

theorem pair173Gap1 :
    RootTracking.OrderedPair (173/3) (row 173 3) (row 174 3) :=
  rise_pair (by decide) root173 root174 (by decide +kernel)

theorem pair173Gap2 :
    RootTracking.OrderedPair (173/3) (row 173 3) (row 175 3) :=
  rise_pair (by decide) root173 root175 (by decide +kernel)

theorem pair173Gap3 :
    RootTracking.OrderedPair (173/3) (row 173 3) (row 176 3) :=
  rise_pair (by decide) root173 root176 (by decide +kernel)

theorem pair174Gap1 :
    RootTracking.OrderedPair (174/3) (row 174 3) (row 175 3) :=
  stay_pair (by decide) root174 root175 (by decide +kernel)

theorem pair174Gap2 :
    RootTracking.OrderedPair (174/3) (row 174 3) (row 176 3) :=
  stay_pair (by decide) root174 root176 (by decide +kernel)

theorem pair174Gap3 :
    RootTracking.OrderedPair (174/3) (row 174 3) (row 177 3) :=
  rise_pair (by decide) root174 root177 (by decide +kernel)

theorem pair175Gap1 :
    RootTracking.OrderedPair (175/3) (row 175 3) (row 176 3) :=
  stay_pair (by decide) root175 root176 (by decide +kernel)

theorem pair175Gap2 :
    RootTracking.OrderedPair (175/3) (row 175 3) (row 177 3) :=
  rise_pair (by decide) root175 root177 (by decide +kernel)

theorem pair175Gap3 :
    RootTracking.OrderedPair (175/3) (row 175 3) (row 178 3) :=
  rise_pair (by decide) root175 root178 (by decide +kernel)

theorem range168Gap1 (n : ℕ) (lo : 168 ≤ n) (hi : n ≤ 175) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair168Gap1
  · exact pair169Gap1
  · exact pair170Gap1
  · exact pair171Gap1
  · exact pair172Gap1
  · exact pair173Gap1
  · exact pair174Gap1
  · exact pair175Gap1

theorem range168Gap2 (n : ℕ) (lo : 168 ≤ n) (hi : n ≤ 175) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair168Gap2
  · exact pair169Gap2
  · exact pair170Gap2
  · exact pair171Gap2
  · exact pair172Gap2
  · exact pair173Gap2
  · exact pair174Gap2
  · exact pair175Gap2

theorem range168Gap3 (n : ℕ) (lo : 168 ≤ n) (hi : n ≤ 175) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair168Gap3
  · exact pair169Gap3
  · exact pair170Gap3
  · exact pair171Gap3
  · exact pair172Gap3
  · exact pair173Gap3
  · exact pair174Gap3
  · exact pair175Gap3


#print axioms range168Gap1
#print axioms range168Gap2
#print axioms range168Gap3

end OrderedPartitions.ThreePoleFinite
