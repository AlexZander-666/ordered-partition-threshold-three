import OrderedPartitions.ThreePoleFiniteData.Counts240

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs240 : signsOK coeffs240 80 boxes240 = true := by
  decide +kernel
theorem root240 : Bracketed 240 boxes240 :=
  bracketed original240 (by decide +kernel) (signAt_of_signsOK signs240)

private theorem signs241 : signsOK coeffs241 80 boxes241 = true := by
  decide +kernel
theorem root241 : Bracketed 241 boxes241 :=
  bracketed original241 (by decide +kernel) (signAt_of_signsOK signs241)

private theorem signs242 : signsOK coeffs242 80 boxes242 = true := by
  decide +kernel
theorem root242 : Bracketed 242 boxes242 :=
  bracketed original242 (by decide +kernel) (signAt_of_signsOK signs242)


#print axioms root242

end OrderedPartitions.ThreePoleFinite
