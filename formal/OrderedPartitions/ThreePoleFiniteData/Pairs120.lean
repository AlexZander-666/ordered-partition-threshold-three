import OrderedPartitions.ThreePoleFiniteData.Roots120
import OrderedPartitions.ThreePoleFiniteData.Roots128

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair120Gap1 :
    RootTracking.OrderedPair (120/3) (row 120 3) (row 121 3) :=
  stay_pair (by decide) root120 root121 (by decide +kernel)

theorem pair120Gap2 :
    RootTracking.OrderedPair (120/3) (row 120 3) (row 122 3) :=
  stay_pair (by decide) root120 root122 (by decide +kernel)

theorem pair120Gap3 :
    RootTracking.OrderedPair (120/3) (row 120 3) (row 123 3) :=
  rise_pair (by decide) root120 root123 (by decide +kernel)

theorem pair121Gap1 :
    RootTracking.OrderedPair (121/3) (row 121 3) (row 122 3) :=
  stay_pair (by decide) root121 root122 (by decide +kernel)

theorem pair121Gap2 :
    RootTracking.OrderedPair (121/3) (row 121 3) (row 123 3) :=
  rise_pair (by decide) root121 root123 (by decide +kernel)

theorem pair121Gap3 :
    RootTracking.OrderedPair (121/3) (row 121 3) (row 124 3) :=
  rise_pair (by decide) root121 root124 (by decide +kernel)

theorem pair122Gap1 :
    RootTracking.OrderedPair (122/3) (row 122 3) (row 123 3) :=
  rise_pair (by decide) root122 root123 (by decide +kernel)

theorem pair122Gap2 :
    RootTracking.OrderedPair (122/3) (row 122 3) (row 124 3) :=
  rise_pair (by decide) root122 root124 (by decide +kernel)

theorem pair122Gap3 :
    RootTracking.OrderedPair (122/3) (row 122 3) (row 125 3) :=
  rise_pair (by decide) root122 root125 (by decide +kernel)

theorem pair123Gap1 :
    RootTracking.OrderedPair (123/3) (row 123 3) (row 124 3) :=
  stay_pair (by decide) root123 root124 (by decide +kernel)

theorem pair123Gap2 :
    RootTracking.OrderedPair (123/3) (row 123 3) (row 125 3) :=
  stay_pair (by decide) root123 root125 (by decide +kernel)

theorem pair123Gap3 :
    RootTracking.OrderedPair (123/3) (row 123 3) (row 126 3) :=
  rise_pair (by decide) root123 root126 (by decide +kernel)

theorem pair124Gap1 :
    RootTracking.OrderedPair (124/3) (row 124 3) (row 125 3) :=
  stay_pair (by decide) root124 root125 (by decide +kernel)

theorem pair124Gap2 :
    RootTracking.OrderedPair (124/3) (row 124 3) (row 126 3) :=
  rise_pair (by decide) root124 root126 (by decide +kernel)

theorem pair124Gap3 :
    RootTracking.OrderedPair (124/3) (row 124 3) (row 127 3) :=
  rise_pair (by decide) root124 root127 (by decide +kernel)

theorem pair125Gap1 :
    RootTracking.OrderedPair (125/3) (row 125 3) (row 126 3) :=
  rise_pair (by decide) root125 root126 (by decide +kernel)

theorem pair125Gap2 :
    RootTracking.OrderedPair (125/3) (row 125 3) (row 127 3) :=
  rise_pair (by decide) root125 root127 (by decide +kernel)

theorem pair125Gap3 :
    RootTracking.OrderedPair (125/3) (row 125 3) (row 128 3) :=
  rise_pair (by decide) root125 root128 (by decide +kernel)

theorem pair126Gap1 :
    RootTracking.OrderedPair (126/3) (row 126 3) (row 127 3) :=
  stay_pair (by decide) root126 root127 (by decide +kernel)

theorem pair126Gap2 :
    RootTracking.OrderedPair (126/3) (row 126 3) (row 128 3) :=
  stay_pair (by decide) root126 root128 (by decide +kernel)

theorem pair126Gap3 :
    RootTracking.OrderedPair (126/3) (row 126 3) (row 129 3) :=
  rise_pair (by decide) root126 root129 (by decide +kernel)

theorem pair127Gap1 :
    RootTracking.OrderedPair (127/3) (row 127 3) (row 128 3) :=
  stay_pair (by decide) root127 root128 (by decide +kernel)

theorem pair127Gap2 :
    RootTracking.OrderedPair (127/3) (row 127 3) (row 129 3) :=
  rise_pair (by decide) root127 root129 (by decide +kernel)

theorem pair127Gap3 :
    RootTracking.OrderedPair (127/3) (row 127 3) (row 130 3) :=
  rise_pair (by decide) root127 root130 (by decide +kernel)

theorem range120Gap1 (n : ℕ) (lo : 120 ≤ n) (hi : n ≤ 127) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair120Gap1
  · exact pair121Gap1
  · exact pair122Gap1
  · exact pair123Gap1
  · exact pair124Gap1
  · exact pair125Gap1
  · exact pair126Gap1
  · exact pair127Gap1

theorem range120Gap2 (n : ℕ) (lo : 120 ≤ n) (hi : n ≤ 127) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair120Gap2
  · exact pair121Gap2
  · exact pair122Gap2
  · exact pair123Gap2
  · exact pair124Gap2
  · exact pair125Gap2
  · exact pair126Gap2
  · exact pair127Gap2

theorem range120Gap3 (n : ℕ) (lo : 120 ≤ n) (hi : n ≤ 127) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair120Gap3
  · exact pair121Gap3
  · exact pair122Gap3
  · exact pair123Gap3
  · exact pair124Gap3
  · exact pair125Gap3
  · exact pair126Gap3
  · exact pair127Gap3


#print axioms range120Gap1
#print axioms range120Gap2
#print axioms range120Gap3

end OrderedPartitions.ThreePoleFinite
