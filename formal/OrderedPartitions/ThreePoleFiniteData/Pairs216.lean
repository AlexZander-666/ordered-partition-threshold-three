import OrderedPartitions.ThreePoleFiniteData.Roots216
import OrderedPartitions.ThreePoleFiniteData.Roots224

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair216Gap1 :
    RootTracking.OrderedPair (216/3) (row 216 3) (row 217 3) :=
  stay_pair (by decide) root216 root217 (by decide +kernel)

theorem pair216Gap2 :
    RootTracking.OrderedPair (216/3) (row 216 3) (row 218 3) :=
  stay_pair (by decide) root216 root218 (by decide +kernel)

theorem pair216Gap3 :
    RootTracking.OrderedPair (216/3) (row 216 3) (row 219 3) :=
  rise_pair (by decide) root216 root219 (by decide +kernel)

theorem pair217Gap1 :
    RootTracking.OrderedPair (217/3) (row 217 3) (row 218 3) :=
  stay_pair (by decide) root217 root218 (by decide +kernel)

theorem pair217Gap2 :
    RootTracking.OrderedPair (217/3) (row 217 3) (row 219 3) :=
  rise_pair (by decide) root217 root219 (by decide +kernel)

theorem pair217Gap3 :
    RootTracking.OrderedPair (217/3) (row 217 3) (row 220 3) :=
  rise_pair (by decide) root217 root220 (by decide +kernel)

theorem pair218Gap1 :
    RootTracking.OrderedPair (218/3) (row 218 3) (row 219 3) :=
  rise_pair (by decide) root218 root219 (by decide +kernel)

theorem pair218Gap2 :
    RootTracking.OrderedPair (218/3) (row 218 3) (row 220 3) :=
  rise_pair (by decide) root218 root220 (by decide +kernel)

theorem pair218Gap3 :
    RootTracking.OrderedPair (218/3) (row 218 3) (row 221 3) :=
  rise_pair (by decide) root218 root221 (by decide +kernel)

theorem pair219Gap1 :
    RootTracking.OrderedPair (219/3) (row 219 3) (row 220 3) :=
  stay_pair (by decide) root219 root220 (by decide +kernel)

theorem pair219Gap2 :
    RootTracking.OrderedPair (219/3) (row 219 3) (row 221 3) :=
  stay_pair (by decide) root219 root221 (by decide +kernel)

theorem pair219Gap3 :
    RootTracking.OrderedPair (219/3) (row 219 3) (row 222 3) :=
  rise_pair (by decide) root219 root222 (by decide +kernel)

theorem pair220Gap1 :
    RootTracking.OrderedPair (220/3) (row 220 3) (row 221 3) :=
  stay_pair (by decide) root220 root221 (by decide +kernel)

theorem pair220Gap2 :
    RootTracking.OrderedPair (220/3) (row 220 3) (row 222 3) :=
  rise_pair (by decide) root220 root222 (by decide +kernel)

theorem pair220Gap3 :
    RootTracking.OrderedPair (220/3) (row 220 3) (row 223 3) :=
  rise_pair (by decide) root220 root223 (by decide +kernel)

theorem pair221Gap1 :
    RootTracking.OrderedPair (221/3) (row 221 3) (row 222 3) :=
  rise_pair (by decide) root221 root222 (by decide +kernel)

theorem pair221Gap2 :
    RootTracking.OrderedPair (221/3) (row 221 3) (row 223 3) :=
  rise_pair (by decide) root221 root223 (by decide +kernel)

theorem pair221Gap3 :
    RootTracking.OrderedPair (221/3) (row 221 3) (row 224 3) :=
  rise_pair (by decide) root221 root224 (by decide +kernel)

theorem pair222Gap1 :
    RootTracking.OrderedPair (222/3) (row 222 3) (row 223 3) :=
  stay_pair (by decide) root222 root223 (by decide +kernel)

theorem pair222Gap2 :
    RootTracking.OrderedPair (222/3) (row 222 3) (row 224 3) :=
  stay_pair (by decide) root222 root224 (by decide +kernel)

theorem pair222Gap3 :
    RootTracking.OrderedPair (222/3) (row 222 3) (row 225 3) :=
  rise_pair (by decide) root222 root225 (by decide +kernel)

theorem pair223Gap1 :
    RootTracking.OrderedPair (223/3) (row 223 3) (row 224 3) :=
  stay_pair (by decide) root223 root224 (by decide +kernel)

theorem pair223Gap2 :
    RootTracking.OrderedPair (223/3) (row 223 3) (row 225 3) :=
  rise_pair (by decide) root223 root225 (by decide +kernel)

theorem pair223Gap3 :
    RootTracking.OrderedPair (223/3) (row 223 3) (row 226 3) :=
  rise_pair (by decide) root223 root226 (by decide +kernel)

theorem range216Gap1 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+1) 3) := by
  interval_cases n
  · exact pair216Gap1
  · exact pair217Gap1
  · exact pair218Gap1
  · exact pair219Gap1
  · exact pair220Gap1
  · exact pair221Gap1
  · exact pair222Gap1
  · exact pair223Gap1

theorem range216Gap2 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+2) 3) := by
  interval_cases n
  · exact pair216Gap2
  · exact pair217Gap2
  · exact pair218Gap2
  · exact pair219Gap2
  · exact pair220Gap2
  · exact pair221Gap2
  · exact pair222Gap2
  · exact pair223Gap2

theorem range216Gap3 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/3) (row n 3) (row (n+3) 3) := by
  interval_cases n
  · exact pair216Gap3
  · exact pair217Gap3
  · exact pair218Gap3
  · exact pair219Gap3
  · exact pair220Gap3
  · exact pair221Gap3
  · exact pair222Gap3
  · exact pair223Gap3


#print axioms range216Gap1
#print axioms range216Gap2
#print axioms range216Gap3

end OrderedPartitions.ThreePoleFinite
