import OrderedPartitions.ThreePoleFiniteData.Counts200

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs200 : signsOK coeffs200 66 boxes200 = true := by
  decide +kernel
theorem root200 : Bracketed 200 boxes200 :=
  bracketed original200 (by decide +kernel) (signAt_of_signsOK signs200)

private theorem signs201 : signsOK coeffs201 67 boxes201 = true := by
  decide +kernel
theorem root201 : Bracketed 201 boxes201 :=
  bracketed original201 (by decide +kernel) (signAt_of_signsOK signs201)

private theorem signs202 : signsOK coeffs202 67 boxes202 = true := by
  decide +kernel
theorem root202 : Bracketed 202 boxes202 :=
  bracketed original202 (by decide +kernel) (signAt_of_signsOK signs202)

private theorem signs203 : signsOK coeffs203 67 boxes203 = true := by
  decide +kernel
theorem root203 : Bracketed 203 boxes203 :=
  bracketed original203 (by decide +kernel) (signAt_of_signsOK signs203)

private theorem signs204 : signsOK coeffs204 68 boxes204 = true := by
  decide +kernel
theorem root204 : Bracketed 204 boxes204 :=
  bracketed original204 (by decide +kernel) (signAt_of_signsOK signs204)

private theorem signs205 : signsOK coeffs205 68 boxes205 = true := by
  decide +kernel
theorem root205 : Bracketed 205 boxes205 :=
  bracketed original205 (by decide +kernel) (signAt_of_signsOK signs205)

private theorem signs206 : signsOK coeffs206 68 boxes206 = true := by
  decide +kernel
theorem root206 : Bracketed 206 boxes206 :=
  bracketed original206 (by decide +kernel) (signAt_of_signsOK signs206)

private theorem signs207 : signsOK coeffs207 69 boxes207 = true := by
  decide +kernel
theorem root207 : Bracketed 207 boxes207 :=
  bracketed original207 (by decide +kernel) (signAt_of_signsOK signs207)


#print axioms root207

end OrderedPartitions.ThreePoleFinite
