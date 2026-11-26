import OrderedPartitions.ThreePoleFiniteData.Counts048

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs48 : signsOK coeffs48 16 boxes48 = true := by
  decide +kernel
theorem root48 : Bracketed 48 boxes48 :=
  bracketed original48 (by decide +kernel) (signAt_of_signsOK signs48)

private theorem signs49 : signsOK coeffs49 16 boxes49 = true := by
  decide +kernel
theorem root49 : Bracketed 49 boxes49 :=
  bracketed original49 (by decide +kernel) (signAt_of_signsOK signs49)

private theorem signs50 : signsOK coeffs50 16 boxes50 = true := by
  decide +kernel
theorem root50 : Bracketed 50 boxes50 :=
  bracketed original50 (by decide +kernel) (signAt_of_signsOK signs50)

private theorem signs51 : signsOK coeffs51 17 boxes51 = true := by
  decide +kernel
theorem root51 : Bracketed 51 boxes51 :=
  bracketed original51 (by decide +kernel) (signAt_of_signsOK signs51)

private theorem signs52 : signsOK coeffs52 17 boxes52 = true := by
  decide +kernel
theorem root52 : Bracketed 52 boxes52 :=
  bracketed original52 (by decide +kernel) (signAt_of_signsOK signs52)

private theorem signs53 : signsOK coeffs53 17 boxes53 = true := by
  decide +kernel
theorem root53 : Bracketed 53 boxes53 :=
  bracketed original53 (by decide +kernel) (signAt_of_signsOK signs53)

private theorem signs54 : signsOK coeffs54 18 boxes54 = true := by
  decide +kernel
theorem root54 : Bracketed 54 boxes54 :=
  bracketed original54 (by decide +kernel) (signAt_of_signsOK signs54)

private theorem signs55 : signsOK coeffs55 18 boxes55 = true := by
  decide +kernel
theorem root55 : Bracketed 55 boxes55 :=
  bracketed original55 (by decide +kernel) (signAt_of_signsOK signs55)


#print axioms root55

end OrderedPartitions.ThreePoleFinite
