import OrderedPartitions.ThreePoleFiniteData.Counts224

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs224 : signsOK coeffs224 74 boxes224 = true := by
  decide +kernel
theorem root224 : Bracketed 224 boxes224 :=
  bracketed original224 (by decide +kernel) (signAt_of_signsOK signs224)

private theorem signs225 : signsOK coeffs225 75 boxes225 = true := by
  decide +kernel
theorem root225 : Bracketed 225 boxes225 :=
  bracketed original225 (by decide +kernel) (signAt_of_signsOK signs225)

private theorem signs226 : signsOK coeffs226 75 boxes226 = true := by
  decide +kernel
theorem root226 : Bracketed 226 boxes226 :=
  bracketed original226 (by decide +kernel) (signAt_of_signsOK signs226)

private theorem signs227 : signsOK coeffs227 75 boxes227 = true := by
  decide +kernel
theorem root227 : Bracketed 227 boxes227 :=
  bracketed original227 (by decide +kernel) (signAt_of_signsOK signs227)

private theorem signs228 : signsOK coeffs228 76 boxes228 = true := by
  decide +kernel
theorem root228 : Bracketed 228 boxes228 :=
  bracketed original228 (by decide +kernel) (signAt_of_signsOK signs228)

private theorem signs229 : signsOK coeffs229 76 boxes229 = true := by
  decide +kernel
theorem root229 : Bracketed 229 boxes229 :=
  bracketed original229 (by decide +kernel) (signAt_of_signsOK signs229)

private theorem signs230 : signsOK coeffs230 76 boxes230 = true := by
  decide +kernel
theorem root230 : Bracketed 230 boxes230 :=
  bracketed original230 (by decide +kernel) (signAt_of_signsOK signs230)

private theorem signs231 : signsOK coeffs231 77 boxes231 = true := by
  decide +kernel
theorem root231 : Bracketed 231 boxes231 :=
  bracketed original231 (by decide +kernel) (signAt_of_signsOK signs231)


#print axioms root231

end OrderedPartitions.ThreePoleFinite
