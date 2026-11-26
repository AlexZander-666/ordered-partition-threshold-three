import OrderedPartitions.ThreePoleFiniteData.Counts040

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs40 : signsOK coeffs40 13 boxes40 = true := by
  decide +kernel
theorem root40 : Bracketed 40 boxes40 :=
  bracketed original40 (by decide +kernel) (signAt_of_signsOK signs40)

private theorem signs41 : signsOK coeffs41 13 boxes41 = true := by
  decide +kernel
theorem root41 : Bracketed 41 boxes41 :=
  bracketed original41 (by decide +kernel) (signAt_of_signsOK signs41)

private theorem signs42 : signsOK coeffs42 14 boxes42 = true := by
  decide +kernel
theorem root42 : Bracketed 42 boxes42 :=
  bracketed original42 (by decide +kernel) (signAt_of_signsOK signs42)

private theorem signs43 : signsOK coeffs43 14 boxes43 = true := by
  decide +kernel
theorem root43 : Bracketed 43 boxes43 :=
  bracketed original43 (by decide +kernel) (signAt_of_signsOK signs43)

private theorem signs44 : signsOK coeffs44 14 boxes44 = true := by
  decide +kernel
theorem root44 : Bracketed 44 boxes44 :=
  bracketed original44 (by decide +kernel) (signAt_of_signsOK signs44)

private theorem signs45 : signsOK coeffs45 15 boxes45 = true := by
  decide +kernel
theorem root45 : Bracketed 45 boxes45 :=
  bracketed original45 (by decide +kernel) (signAt_of_signsOK signs45)

private theorem signs46 : signsOK coeffs46 15 boxes46 = true := by
  decide +kernel
theorem root46 : Bracketed 46 boxes46 :=
  bracketed original46 (by decide +kernel) (signAt_of_signsOK signs46)

private theorem signs47 : signsOK coeffs47 15 boxes47 = true := by
  decide +kernel
theorem root47 : Bracketed 47 boxes47 :=
  bracketed original47 (by decide +kernel) (signAt_of_signsOK signs47)


#print axioms root47

end OrderedPartitions.ThreePoleFinite
