import OrderedPartitions.ThreePoleFiniteData.Counts216

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs216 : signsOK coeffs216 72 boxes216 = true := by
  decide +kernel
theorem root216 : Bracketed 216 boxes216 :=
  bracketed original216 (by decide +kernel) (signAt_of_signsOK signs216)

private theorem signs217 : signsOK coeffs217 72 boxes217 = true := by
  decide +kernel
theorem root217 : Bracketed 217 boxes217 :=
  bracketed original217 (by decide +kernel) (signAt_of_signsOK signs217)

private theorem signs218 : signsOK coeffs218 72 boxes218 = true := by
  decide +kernel
theorem root218 : Bracketed 218 boxes218 :=
  bracketed original218 (by decide +kernel) (signAt_of_signsOK signs218)

private theorem signs219 : signsOK coeffs219 73 boxes219 = true := by
  decide +kernel
theorem root219 : Bracketed 219 boxes219 :=
  bracketed original219 (by decide +kernel) (signAt_of_signsOK signs219)

private theorem signs220 : signsOK coeffs220 73 boxes220 = true := by
  decide +kernel
theorem root220 : Bracketed 220 boxes220 :=
  bracketed original220 (by decide +kernel) (signAt_of_signsOK signs220)

private theorem signs221 : signsOK coeffs221 73 boxes221 = true := by
  decide +kernel
theorem root221 : Bracketed 221 boxes221 :=
  bracketed original221 (by decide +kernel) (signAt_of_signsOK signs221)

private theorem signs222 : signsOK coeffs222 74 boxes222 = true := by
  decide +kernel
theorem root222 : Bracketed 222 boxes222 :=
  bracketed original222 (by decide +kernel) (signAt_of_signsOK signs222)

private theorem signs223 : signsOK coeffs223 74 boxes223 = true := by
  decide +kernel
theorem root223 : Bracketed 223 boxes223 :=
  bracketed original223 (by decide +kernel) (signAt_of_signsOK signs223)


#print axioms root223

end OrderedPartitions.ThreePoleFinite
