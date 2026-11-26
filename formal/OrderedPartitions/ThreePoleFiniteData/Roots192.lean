import OrderedPartitions.ThreePoleFiniteData.Counts192

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs192 : signsOK coeffs192 64 boxes192 = true := by
  decide +kernel
theorem root192 : Bracketed 192 boxes192 :=
  bracketed original192 (by decide +kernel) (signAt_of_signsOK signs192)

private theorem signs193 : signsOK coeffs193 64 boxes193 = true := by
  decide +kernel
theorem root193 : Bracketed 193 boxes193 :=
  bracketed original193 (by decide +kernel) (signAt_of_signsOK signs193)

private theorem signs194 : signsOK coeffs194 64 boxes194 = true := by
  decide +kernel
theorem root194 : Bracketed 194 boxes194 :=
  bracketed original194 (by decide +kernel) (signAt_of_signsOK signs194)

private theorem signs195 : signsOK coeffs195 65 boxes195 = true := by
  decide +kernel
theorem root195 : Bracketed 195 boxes195 :=
  bracketed original195 (by decide +kernel) (signAt_of_signsOK signs195)

private theorem signs196 : signsOK coeffs196 65 boxes196 = true := by
  decide +kernel
theorem root196 : Bracketed 196 boxes196 :=
  bracketed original196 (by decide +kernel) (signAt_of_signsOK signs196)

private theorem signs197 : signsOK coeffs197 65 boxes197 = true := by
  decide +kernel
theorem root197 : Bracketed 197 boxes197 :=
  bracketed original197 (by decide +kernel) (signAt_of_signsOK signs197)

private theorem signs198 : signsOK coeffs198 66 boxes198 = true := by
  decide +kernel
theorem root198 : Bracketed 198 boxes198 :=
  bracketed original198 (by decide +kernel) (signAt_of_signsOK signs198)

private theorem signs199 : signsOK coeffs199 66 boxes199 = true := by
  decide +kernel
theorem root199 : Bracketed 199 boxes199 :=
  bracketed original199 (by decide +kernel) (signAt_of_signsOK signs199)


#print axioms root199

end OrderedPartitions.ThreePoleFinite
