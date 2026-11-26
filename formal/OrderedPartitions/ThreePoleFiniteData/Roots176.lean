import OrderedPartitions.ThreePoleFiniteData.Counts176

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs176 : signsOK coeffs176 58 boxes176 = true := by
  decide +kernel
theorem root176 : Bracketed 176 boxes176 :=
  bracketed original176 (by decide +kernel) (signAt_of_signsOK signs176)

private theorem signs177 : signsOK coeffs177 59 boxes177 = true := by
  decide +kernel
theorem root177 : Bracketed 177 boxes177 :=
  bracketed original177 (by decide +kernel) (signAt_of_signsOK signs177)

private theorem signs178 : signsOK coeffs178 59 boxes178 = true := by
  decide +kernel
theorem root178 : Bracketed 178 boxes178 :=
  bracketed original178 (by decide +kernel) (signAt_of_signsOK signs178)

private theorem signs179 : signsOK coeffs179 59 boxes179 = true := by
  decide +kernel
theorem root179 : Bracketed 179 boxes179 :=
  bracketed original179 (by decide +kernel) (signAt_of_signsOK signs179)

private theorem signs180 : signsOK coeffs180 60 boxes180 = true := by
  decide +kernel
theorem root180 : Bracketed 180 boxes180 :=
  bracketed original180 (by decide +kernel) (signAt_of_signsOK signs180)

private theorem signs181 : signsOK coeffs181 60 boxes181 = true := by
  decide +kernel
theorem root181 : Bracketed 181 boxes181 :=
  bracketed original181 (by decide +kernel) (signAt_of_signsOK signs181)

private theorem signs182 : signsOK coeffs182 60 boxes182 = true := by
  decide +kernel
theorem root182 : Bracketed 182 boxes182 :=
  bracketed original182 (by decide +kernel) (signAt_of_signsOK signs182)

private theorem signs183 : signsOK coeffs183 61 boxes183 = true := by
  decide +kernel
theorem root183 : Bracketed 183 boxes183 :=
  bracketed original183 (by decide +kernel) (signAt_of_signsOK signs183)


#print axioms root183

end OrderedPartitions.ThreePoleFinite
