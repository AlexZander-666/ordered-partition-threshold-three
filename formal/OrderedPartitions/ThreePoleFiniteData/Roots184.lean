import OrderedPartitions.ThreePoleFiniteData.Counts184

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs184 : signsOK coeffs184 61 boxes184 = true := by
  decide +kernel
theorem root184 : Bracketed 184 boxes184 :=
  bracketed original184 (by decide +kernel) (signAt_of_signsOK signs184)

private theorem signs185 : signsOK coeffs185 61 boxes185 = true := by
  decide +kernel
theorem root185 : Bracketed 185 boxes185 :=
  bracketed original185 (by decide +kernel) (signAt_of_signsOK signs185)

private theorem signs186 : signsOK coeffs186 62 boxes186 = true := by
  decide +kernel
theorem root186 : Bracketed 186 boxes186 :=
  bracketed original186 (by decide +kernel) (signAt_of_signsOK signs186)

private theorem signs187 : signsOK coeffs187 62 boxes187 = true := by
  decide +kernel
theorem root187 : Bracketed 187 boxes187 :=
  bracketed original187 (by decide +kernel) (signAt_of_signsOK signs187)

private theorem signs188 : signsOK coeffs188 62 boxes188 = true := by
  decide +kernel
theorem root188 : Bracketed 188 boxes188 :=
  bracketed original188 (by decide +kernel) (signAt_of_signsOK signs188)

private theorem signs189 : signsOK coeffs189 63 boxes189 = true := by
  decide +kernel
theorem root189 : Bracketed 189 boxes189 :=
  bracketed original189 (by decide +kernel) (signAt_of_signsOK signs189)

private theorem signs190 : signsOK coeffs190 63 boxes190 = true := by
  decide +kernel
theorem root190 : Bracketed 190 boxes190 :=
  bracketed original190 (by decide +kernel) (signAt_of_signsOK signs190)

private theorem signs191 : signsOK coeffs191 63 boxes191 = true := by
  decide +kernel
theorem root191 : Bracketed 191 boxes191 :=
  bracketed original191 (by decide +kernel) (signAt_of_signsOK signs191)


#print axioms root191

end OrderedPartitions.ThreePoleFinite
