import OrderedPartitions.ThreePoleFiniteData.Roots176
import OrderedPartitions.ThreePoleFiniteData.Roots184

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair176Gap1 :
    RootTracking.OrderedPair (176/3) (row 176 3) (row 177 3) :=
  rise_pair (by decide) root176 root177 (by decide +kernel)

theorem pair176Gap2 :
    RootTracking.OrderedPair (176/3) (row 176 3) (row 178 3) :=
  rise_pair (by decide) root176 root178 (by decide +kernel)

theorem pair176Gap3 :
    RootTracking.OrderedPair (176/3) (row 176 3) (row 179 3) :=
  rise_pair (by decide) root176 root179 (by decide +kernel)

theorem pair177Gap1 :
    RootTracking.OrderedPair (177/3) (row 177 3) (row 178 3) :=
  stay_pair (by decide) root177 root178 (by decide +kernel)

theorem pair177Gap2 :
    RootTracking.OrderedPair (177/3) (row 177 3) (row 179 3) :=
  stay_pair (by decide) root177 root179 (by decide +kernel)

theorem pair177Gap3 :
    RootTracking.OrderedPair (177/3) (row 177 3) (row 180 3) :=
  rise_pair (by decide) root177 root180 (by decide +kernel)

theorem pair178Gap1 :
    RootTracking.OrderedPair (178/3) (row 178 3) (row 179 3) :=
  stay_pair (by decide) root178 root179 (by decide +kernel)

theorem pair178Gap2 :
    RootTracking.OrderedPair (178/3) (row 178 3) (row 180 3) :=
  rise_pair (by decide) root178 root180 (by decide +kernel)

theorem pair178Gap3 :
    RootTracking.OrderedPair (178/3) (row 178 3) (row 181 3) :=
  rise_pair (by decide) root178 root181 (by decide +kernel)

theorem pair179Gap1 :
    RootTracking.OrderedPair (179/3) (row 179 3) (row 180 3) :=
  rise_pair (by decide) root179 root180 (by decide +kernel)

theorem pair179Gap2 :
    RootTracking.OrderedPair (179/3) (row 179 3) (row 181 3) :=
  rise_pair (by decide) root179 root181 (by decide +kernel)

theorem pair179Gap3 :
    RootTracking.OrderedPair (179/3) (row 179 3) (row 182 3) :=
  rise_pair (by decide) root179 root182 (by decide +kernel)

theorem pair180Gap1 :
    RootTracking.OrderedPair (180/3) (row 180 3) (row 181 3) :=
  stay_pair (by decide) root180 root181 (by decide +kernel)

theorem pair180Gap2 :
    RootTracking.OrderedPair (180/3) (row 180 3) (row 182 3) :=
  stay_pair (by decide) root180 root182 (by decide +kernel)

theorem pair180Gap3 :
    RootTracking.OrderedPair (180/3) (row 180 3) (row 183 3) :=
  rise_pair (by decide) root180 root183 (by decide +kernel)

theorem pair181Gap1 :
    RootTracking.OrderedPair (181/3) (row 181 3) (row 182 3) :=
  stay_pair (by decide) root181 root182 (by decide +kernel)

theorem pair181Gap2 :
    RootTracking.OrderedPair (181/3) (row 181 3) (row 183 3) :=
  rise_pair (by decide) root181 root183 (by decide +kernel)

theorem pair181Gap3 :
    RootTracking.OrderedPair (181/3) (row 181 3) (row 184 3) :=
  rise_pair (by decide) root181 root184 (by decide +kernel)

theorem pair182Gap1 :
    RootTracking.OrderedPair (182/3) (row 182 3) (row 183 3) :=
  rise_pair (by decide) root182 root183 (by decide +kernel)

theorem pair182Gap2 :
    RootTracking.OrderedPair (182/3) (row 182 3) (row 184 3) :=
  rise_pair (by decide) root182 root184 (by decide +kernel)

theorem pair182Gap3 :
    RootTracking.OrderedPair (182/3) (row 182 3) (row 185 3) :=
  rise_pair (by decide) root182 root185 (by decide +kernel)

theorem pair183Gap1 :
    RootTracking.OrderedPair (183/3) (row 183 3) (row 184 3) :=
  stay_pair (by decide) root183 root184 (by decide +kernel)

theorem pair183Gap2 :
    RootTracking.OrderedPair (183/3) (row 183 3) (row 185 3) :=
  stay_pair (by decide) root183 root185 (by decide +kernel)

theorem pair183Gap3 :
    RootTracking.OrderedPair (183/3) (row 183 3) (row 186 3) :=
  rise_pair (by decide) root183 root186 (by decide +kernel)

theorem range176Gap1 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair176Gap1
  · exact pair177Gap1
  · exact pair178Gap1
  · exact pair179Gap1
  · exact pair180Gap1
  · exact pair181Gap1
  · exact pair182Gap1
  · exact pair183Gap1

theorem range176Gap2 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair176Gap2
  · exact pair177Gap2
  · exact pair178Gap2
  · exact pair179Gap2
  · exact pair180Gap2
  · exact pair181Gap2
  · exact pair182Gap2
  · exact pair183Gap2

theorem range176Gap3 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair176Gap3
  · exact pair177Gap3
  · exact pair178Gap3
  · exact pair179Gap3
  · exact pair180Gap3
  · exact pair181Gap3
  · exact pair182Gap3
  · exact pair183Gap3


#print axioms range176Gap1
#print axioms range176Gap2
#print axioms range176Gap3

end OrderedPartitions.ThreePoleFinite
