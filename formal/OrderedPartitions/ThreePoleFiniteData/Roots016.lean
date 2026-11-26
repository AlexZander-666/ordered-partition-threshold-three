import OrderedPartitions.ThreePoleFiniteData.Counts016

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs16 : signsOK coeffs16 5 boxes16 = true := by
  decide +kernel
theorem root16 : Bracketed 16 boxes16 :=
  bracketed original16 (by decide +kernel) (signAt_of_signsOK signs16)

private theorem signs17 : signsOK coeffs17 5 boxes17 = true := by
  decide +kernel
theorem root17 : Bracketed 17 boxes17 :=
  bracketed original17 (by decide +kernel) (signAt_of_signsOK signs17)

private theorem signs18 : signsOK coeffs18 6 boxes18 = true := by
  decide +kernel
theorem root18 : Bracketed 18 boxes18 :=
  bracketed original18 (by decide +kernel) (signAt_of_signsOK signs18)

private theorem signs19 : signsOK coeffs19 6 boxes19 = true := by
  decide +kernel
theorem root19 : Bracketed 19 boxes19 :=
  bracketed original19 (by decide +kernel) (signAt_of_signsOK signs19)

private theorem signs20 : signsOK coeffs20 6 boxes20 = true := by
  decide +kernel
theorem root20 : Bracketed 20 boxes20 :=
  bracketed original20 (by decide +kernel) (signAt_of_signsOK signs20)

private theorem signs21 : signsOK coeffs21 7 boxes21 = true := by
  decide +kernel
theorem root21 : Bracketed 21 boxes21 :=
  bracketed original21 (by decide +kernel) (signAt_of_signsOK signs21)

private theorem signs22 : signsOK coeffs22 7 boxes22 = true := by
  decide +kernel
theorem root22 : Bracketed 22 boxes22 :=
  bracketed original22 (by decide +kernel) (signAt_of_signsOK signs22)

private theorem signs23 : signsOK coeffs23 7 boxes23 = true := by
  decide +kernel
theorem root23 : Bracketed 23 boxes23 :=
  bracketed original23 (by decide +kernel) (signAt_of_signsOK signs23)


#print axioms root23

end OrderedPartitions.ThreePoleFinite
