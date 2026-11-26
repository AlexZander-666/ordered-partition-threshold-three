import OrderedPartitions.ThreePoleFiniteData.Counts080

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs80 : signsOK coeffs80 26 boxes80 = true := by
  decide +kernel
theorem root80 : Bracketed 80 boxes80 :=
  bracketed original80 (by decide +kernel) (signAt_of_signsOK signs80)

private theorem signs81 : signsOK coeffs81 27 boxes81 = true := by
  decide +kernel
theorem root81 : Bracketed 81 boxes81 :=
  bracketed original81 (by decide +kernel) (signAt_of_signsOK signs81)

private theorem signs82 : signsOK coeffs82 27 boxes82 = true := by
  decide +kernel
theorem root82 : Bracketed 82 boxes82 :=
  bracketed original82 (by decide +kernel) (signAt_of_signsOK signs82)

private theorem signs83 : signsOK coeffs83 27 boxes83 = true := by
  decide +kernel
theorem root83 : Bracketed 83 boxes83 :=
  bracketed original83 (by decide +kernel) (signAt_of_signsOK signs83)

private theorem signs84 : signsOK coeffs84 28 boxes84 = true := by
  decide +kernel
theorem root84 : Bracketed 84 boxes84 :=
  bracketed original84 (by decide +kernel) (signAt_of_signsOK signs84)

private theorem signs85 : signsOK coeffs85 28 boxes85 = true := by
  decide +kernel
theorem root85 : Bracketed 85 boxes85 :=
  bracketed original85 (by decide +kernel) (signAt_of_signsOK signs85)

private theorem signs86 : signsOK coeffs86 28 boxes86 = true := by
  decide +kernel
theorem root86 : Bracketed 86 boxes86 :=
  bracketed original86 (by decide +kernel) (signAt_of_signsOK signs86)

private theorem signs87 : signsOK coeffs87 29 boxes87 = true := by
  decide +kernel
theorem root87 : Bracketed 87 boxes87 :=
  bracketed original87 (by decide +kernel) (signAt_of_signsOK signs87)


#print axioms root87

end OrderedPartitions.ThreePoleFinite
