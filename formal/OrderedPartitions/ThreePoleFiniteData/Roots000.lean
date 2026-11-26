import OrderedPartitions.ThreePoleFiniteData.Counts000

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs0 : signsOK coeffs0 0 boxes0 = true := by
  decide +kernel
theorem root0 : Bracketed 0 boxes0 :=
  bracketed original0 (by decide +kernel) (signAt_of_signsOK signs0)

private theorem signs1 : signsOK coeffs1 0 boxes1 = true := by
  decide +kernel
theorem root1 : Bracketed 1 boxes1 :=
  bracketed original1 (by decide +kernel) (signAt_of_signsOK signs1)

private theorem signs2 : signsOK coeffs2 0 boxes2 = true := by
  decide +kernel
theorem root2 : Bracketed 2 boxes2 :=
  bracketed original2 (by decide +kernel) (signAt_of_signsOK signs2)

private theorem signs3 : signsOK coeffs3 1 boxes3 = true := by
  decide +kernel
theorem root3 : Bracketed 3 boxes3 :=
  bracketed original3 (by decide +kernel) (signAt_of_signsOK signs3)

private theorem signs4 : signsOK coeffs4 1 boxes4 = true := by
  decide +kernel
theorem root4 : Bracketed 4 boxes4 :=
  bracketed original4 (by decide +kernel) (signAt_of_signsOK signs4)

private theorem signs5 : signsOK coeffs5 1 boxes5 = true := by
  decide +kernel
theorem root5 : Bracketed 5 boxes5 :=
  bracketed original5 (by decide +kernel) (signAt_of_signsOK signs5)

private theorem signs6 : signsOK coeffs6 2 boxes6 = true := by
  decide +kernel
theorem root6 : Bracketed 6 boxes6 :=
  bracketed original6 (by decide +kernel) (signAt_of_signsOK signs6)

private theorem signs7 : signsOK coeffs7 2 boxes7 = true := by
  decide +kernel
theorem root7 : Bracketed 7 boxes7 :=
  bracketed original7 (by decide +kernel) (signAt_of_signsOK signs7)


#print axioms root7

end OrderedPartitions.ThreePoleFinite
