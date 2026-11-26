import OrderedPartitions.ThreePoleFiniteData.Counts128

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs128 : signsOK coeffs128 42 boxes128 = true := by
  decide +kernel
theorem root128 : Bracketed 128 boxes128 :=
  bracketed original128 (by decide +kernel) (signAt_of_signsOK signs128)

private theorem signs129 : signsOK coeffs129 43 boxes129 = true := by
  decide +kernel
theorem root129 : Bracketed 129 boxes129 :=
  bracketed original129 (by decide +kernel) (signAt_of_signsOK signs129)

private theorem signs130 : signsOK coeffs130 43 boxes130 = true := by
  decide +kernel
theorem root130 : Bracketed 130 boxes130 :=
  bracketed original130 (by decide +kernel) (signAt_of_signsOK signs130)

private theorem signs131 : signsOK coeffs131 43 boxes131 = true := by
  decide +kernel
theorem root131 : Bracketed 131 boxes131 :=
  bracketed original131 (by decide +kernel) (signAt_of_signsOK signs131)

private theorem signs132 : signsOK coeffs132 44 boxes132 = true := by
  decide +kernel
theorem root132 : Bracketed 132 boxes132 :=
  bracketed original132 (by decide +kernel) (signAt_of_signsOK signs132)

private theorem signs133 : signsOK coeffs133 44 boxes133 = true := by
  decide +kernel
theorem root133 : Bracketed 133 boxes133 :=
  bracketed original133 (by decide +kernel) (signAt_of_signsOK signs133)

private theorem signs134 : signsOK coeffs134 44 boxes134 = true := by
  decide +kernel
theorem root134 : Bracketed 134 boxes134 :=
  bracketed original134 (by decide +kernel) (signAt_of_signsOK signs134)

private theorem signs135 : signsOK coeffs135 45 boxes135 = true := by
  decide +kernel
theorem root135 : Bracketed 135 boxes135 :=
  bracketed original135 (by decide +kernel) (signAt_of_signsOK signs135)


#print axioms root135

end OrderedPartitions.ThreePoleFinite
