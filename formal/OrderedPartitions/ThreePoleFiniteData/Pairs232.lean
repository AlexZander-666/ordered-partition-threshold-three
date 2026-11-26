import OrderedPartitions.ThreePoleFiniteData.Roots232
import OrderedPartitions.ThreePoleFiniteData.Roots240

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair232Gap1 :
    RootTracking.OrderedPair (232/3) (row 232 3) (row 233 3) :=
  stay_pair (by decide) root232 root233 (by decide +kernel)

theorem pair232Gap2 :
    RootTracking.OrderedPair (232/3) (row 232 3) (row 234 3) :=
  rise_pair (by decide) root232 root234 (by decide +kernel)

theorem pair232Gap3 :
    RootTracking.OrderedPair (232/3) (row 232 3) (row 235 3) :=
  rise_pair (by decide) root232 root235 (by decide +kernel)

theorem pair233Gap1 :
    RootTracking.OrderedPair (233/3) (row 233 3) (row 234 3) :=
  rise_pair (by decide) root233 root234 (by decide +kernel)

theorem pair233Gap2 :
    RootTracking.OrderedPair (233/3) (row 233 3) (row 235 3) :=
  rise_pair (by decide) root233 root235 (by decide +kernel)

theorem pair233Gap3 :
    RootTracking.OrderedPair (233/3) (row 233 3) (row 236 3) :=
  rise_pair (by decide) root233 root236 (by decide +kernel)

theorem pair234Gap1 :
    RootTracking.OrderedPair (234/3) (row 234 3) (row 235 3) :=
  stay_pair (by decide) root234 root235 (by decide +kernel)

theorem pair234Gap2 :
    RootTracking.OrderedPair (234/3) (row 234 3) (row 236 3) :=
  stay_pair (by decide) root234 root236 (by decide +kernel)

theorem pair234Gap3 :
    RootTracking.OrderedPair (234/3) (row 234 3) (row 237 3) :=
  rise_pair (by decide) root234 root237 (by decide +kernel)

theorem pair235Gap1 :
    RootTracking.OrderedPair (235/3) (row 235 3) (row 236 3) :=
  stay_pair (by decide) root235 root236 (by decide +kernel)

theorem pair235Gap2 :
    RootTracking.OrderedPair (235/3) (row 235 3) (row 237 3) :=
  rise_pair (by decide) root235 root237 (by decide +kernel)

theorem pair235Gap3 :
    RootTracking.OrderedPair (235/3) (row 235 3) (row 238 3) :=
  rise_pair (by decide) root235 root238 (by decide +kernel)

theorem pair236Gap1 :
    RootTracking.OrderedPair (236/3) (row 236 3) (row 237 3) :=
  rise_pair (by decide) root236 root237 (by decide +kernel)

theorem pair236Gap2 :
    RootTracking.OrderedPair (236/3) (row 236 3) (row 238 3) :=
  rise_pair (by decide) root236 root238 (by decide +kernel)

theorem pair236Gap3 :
    RootTracking.OrderedPair (236/3) (row 236 3) (row 239 3) :=
  rise_pair (by decide) root236 root239 (by decide +kernel)

theorem pair237Gap1 :
    RootTracking.OrderedPair (237/3) (row 237 3) (row 238 3) :=
  stay_pair (by decide) root237 root238 (by decide +kernel)

theorem pair237Gap2 :
    RootTracking.OrderedPair (237/3) (row 237 3) (row 239 3) :=
  stay_pair (by decide) root237 root239 (by decide +kernel)

theorem pair237Gap3 :
    RootTracking.OrderedPair (237/3) (row 237 3) (row 240 3) :=
  rise_pair (by decide) root237 root240 (by decide +kernel)

theorem pair238Gap1 :
    RootTracking.OrderedPair (238/3) (row 238 3) (row 239 3) :=
  stay_pair (by decide) root238 root239 (by decide +kernel)

theorem pair238Gap2 :
    RootTracking.OrderedPair (238/3) (row 238 3) (row 240 3) :=
  rise_pair (by decide) root238 root240 (by decide +kernel)

theorem pair238Gap3 :
    RootTracking.OrderedPair (238/3) (row 238 3) (row 241 3) :=
  rise_pair (by decide) root238 root241 (by decide +kernel)

theorem pair239Gap1 :
    RootTracking.OrderedPair (239/3) (row 239 3) (row 240 3) :=
  rise_pair (by decide) root239 root240 (by decide +kernel)

theorem pair239Gap2 :
    RootTracking.OrderedPair (239/3) (row 239 3) (row 241 3) :=
  rise_pair (by decide) root239 root241 (by decide +kernel)

theorem pair239Gap3 :
    RootTracking.OrderedPair (239/3) (row 239 3) (row 242 3) :=
  rise_pair (by decide) root239 root242 (by decide +kernel)

theorem range232Gap1 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair232Gap1
  · exact pair233Gap1
  · exact pair234Gap1
  · exact pair235Gap1
  · exact pair236Gap1
  · exact pair237Gap1
  · exact pair238Gap1
  · exact pair239Gap1

theorem range232Gap2 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair232Gap2
  · exact pair233Gap2
  · exact pair234Gap2
  · exact pair235Gap2
  · exact pair236Gap2
  · exact pair237Gap2
  · exact pair238Gap2
  · exact pair239Gap2

theorem range232Gap3 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair232Gap3
  · exact pair233Gap3
  · exact pair234Gap3
  · exact pair235Gap3
  · exact pair236Gap3
  · exact pair237Gap3
  · exact pair238Gap3
  · exact pair239Gap3


#print axioms range232Gap1
#print axioms range232Gap2
#print axioms range232Gap3

end OrderedPartitions.ThreePoleFinite
