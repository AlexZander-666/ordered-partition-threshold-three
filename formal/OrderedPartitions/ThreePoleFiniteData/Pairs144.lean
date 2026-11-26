import OrderedPartitions.ThreePoleFiniteData.Roots144
import OrderedPartitions.ThreePoleFiniteData.Roots152

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair144Gap1 :
    RootTracking.OrderedPair (144/3) (row 144 3) (row 145 3) :=
  stay_pair (by decide) root144 root145 (by decide +kernel)

theorem pair144Gap2 :
    RootTracking.OrderedPair (144/3) (row 144 3) (row 146 3) :=
  stay_pair (by decide) root144 root146 (by decide +kernel)

theorem pair144Gap3 :
    RootTracking.OrderedPair (144/3) (row 144 3) (row 147 3) :=
  rise_pair (by decide) root144 root147 (by decide +kernel)

theorem pair145Gap1 :
    RootTracking.OrderedPair (145/3) (row 145 3) (row 146 3) :=
  stay_pair (by decide) root145 root146 (by decide +kernel)

theorem pair145Gap2 :
    RootTracking.OrderedPair (145/3) (row 145 3) (row 147 3) :=
  rise_pair (by decide) root145 root147 (by decide +kernel)

theorem pair145Gap3 :
    RootTracking.OrderedPair (145/3) (row 145 3) (row 148 3) :=
  rise_pair (by decide) root145 root148 (by decide +kernel)

theorem pair146Gap1 :
    RootTracking.OrderedPair (146/3) (row 146 3) (row 147 3) :=
  rise_pair (by decide) root146 root147 (by decide +kernel)

theorem pair146Gap2 :
    RootTracking.OrderedPair (146/3) (row 146 3) (row 148 3) :=
  rise_pair (by decide) root146 root148 (by decide +kernel)

theorem pair146Gap3 :
    RootTracking.OrderedPair (146/3) (row 146 3) (row 149 3) :=
  rise_pair (by decide) root146 root149 (by decide +kernel)

theorem pair147Gap1 :
    RootTracking.OrderedPair (147/3) (row 147 3) (row 148 3) :=
  stay_pair (by decide) root147 root148 (by decide +kernel)

theorem pair147Gap2 :
    RootTracking.OrderedPair (147/3) (row 147 3) (row 149 3) :=
  stay_pair (by decide) root147 root149 (by decide +kernel)

theorem pair147Gap3 :
    RootTracking.OrderedPair (147/3) (row 147 3) (row 150 3) :=
  rise_pair (by decide) root147 root150 (by decide +kernel)

theorem pair148Gap1 :
    RootTracking.OrderedPair (148/3) (row 148 3) (row 149 3) :=
  stay_pair (by decide) root148 root149 (by decide +kernel)

theorem pair148Gap2 :
    RootTracking.OrderedPair (148/3) (row 148 3) (row 150 3) :=
  rise_pair (by decide) root148 root150 (by decide +kernel)

theorem pair148Gap3 :
    RootTracking.OrderedPair (148/3) (row 148 3) (row 151 3) :=
  rise_pair (by decide) root148 root151 (by decide +kernel)

theorem pair149Gap1 :
    RootTracking.OrderedPair (149/3) (row 149 3) (row 150 3) :=
  rise_pair (by decide) root149 root150 (by decide +kernel)

theorem pair149Gap2 :
    RootTracking.OrderedPair (149/3) (row 149 3) (row 151 3) :=
  rise_pair (by decide) root149 root151 (by decide +kernel)

theorem pair149Gap3 :
    RootTracking.OrderedPair (149/3) (row 149 3) (row 152 3) :=
  rise_pair (by decide) root149 root152 (by decide +kernel)

theorem pair150Gap1 :
    RootTracking.OrderedPair (150/3) (row 150 3) (row 151 3) :=
  stay_pair (by decide) root150 root151 (by decide +kernel)

theorem pair150Gap2 :
    RootTracking.OrderedPair (150/3) (row 150 3) (row 152 3) :=
  stay_pair (by decide) root150 root152 (by decide +kernel)

theorem pair150Gap3 :
    RootTracking.OrderedPair (150/3) (row 150 3) (row 153 3) :=
  rise_pair (by decide) root150 root153 (by decide +kernel)

theorem pair151Gap1 :
    RootTracking.OrderedPair (151/3) (row 151 3) (row 152 3) :=
  stay_pair (by decide) root151 root152 (by decide +kernel)

theorem pair151Gap2 :
    RootTracking.OrderedPair (151/3) (row 151 3) (row 153 3) :=
  rise_pair (by decide) root151 root153 (by decide +kernel)

theorem pair151Gap3 :
    RootTracking.OrderedPair (151/3) (row 151 3) (row 154 3) :=
  rise_pair (by decide) root151 root154 (by decide +kernel)

theorem range144Gap1 (n : ℕ) (lo : 144 ≤ n) (hi : n ≤ 151) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair144Gap1
  · exact pair145Gap1
  · exact pair146Gap1
  · exact pair147Gap1
  · exact pair148Gap1
  · exact pair149Gap1
  · exact pair150Gap1
  · exact pair151Gap1

theorem range144Gap2 (n : ℕ) (lo : 144 ≤ n) (hi : n ≤ 151) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair144Gap2
  · exact pair145Gap2
  · exact pair146Gap2
  · exact pair147Gap2
  · exact pair148Gap2
  · exact pair149Gap2
  · exact pair150Gap2
  · exact pair151Gap2

theorem range144Gap3 (n : ℕ) (lo : 144 ≤ n) (hi : n ≤ 151) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair144Gap3
  · exact pair145Gap3
  · exact pair146Gap3
  · exact pair147Gap3
  · exact pair148Gap3
  · exact pair149Gap3
  · exact pair150Gap3
  · exact pair151Gap3


#print axioms range144Gap1
#print axioms range144Gap2
#print axioms range144Gap3

end OrderedPartitions.ThreePoleFinite
