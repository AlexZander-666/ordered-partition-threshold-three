import OrderedPartitions.ThreePoleFiniteData.Counts008

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs8 : signsOK coeffs8 2 boxes8 = true := by
  decide +kernel
theorem root8 : Bracketed 8 boxes8 :=
  bracketed original8 (by decide +kernel) (signAt_of_signsOK signs8)

private theorem signs9 : signsOK coeffs9 3 boxes9 = true := by
  decide +kernel
theorem root9 : Bracketed 9 boxes9 :=
  bracketed original9 (by decide +kernel) (signAt_of_signsOK signs9)

private theorem signs10 : signsOK coeffs10 3 boxes10 = true := by
  decide +kernel
theorem root10 : Bracketed 10 boxes10 :=
  bracketed original10 (by decide +kernel) (signAt_of_signsOK signs10)

private theorem signs11 : signsOK coeffs11 3 boxes11 = true := by
  decide +kernel
theorem root11 : Bracketed 11 boxes11 :=
  bracketed original11 (by decide +kernel) (signAt_of_signsOK signs11)

private theorem signs12 : signsOK coeffs12 4 boxes12 = true := by
  decide +kernel
theorem root12 : Bracketed 12 boxes12 :=
  bracketed original12 (by decide +kernel) (signAt_of_signsOK signs12)

private theorem signs13 : signsOK coeffs13 4 boxes13 = true := by
  decide +kernel
theorem root13 : Bracketed 13 boxes13 :=
  bracketed original13 (by decide +kernel) (signAt_of_signsOK signs13)

private theorem signs14 : signsOK coeffs14 4 boxes14 = true := by
  decide +kernel
theorem root14 : Bracketed 14 boxes14 :=
  bracketed original14 (by decide +kernel) (signAt_of_signsOK signs14)

private theorem signs15 : signsOK coeffs15 5 boxes15 = true := by
  decide +kernel
theorem root15 : Bracketed 15 boxes15 :=
  bracketed original15 (by decide +kernel) (signAt_of_signsOK signs15)


#print axioms root15

end OrderedPartitions.ThreePoleFinite
