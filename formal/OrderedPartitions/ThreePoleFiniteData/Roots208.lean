import OrderedPartitions.ThreePoleFiniteData.Counts208

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs208 : signsOK coeffs208 69 boxes208 = true := by
  decide +kernel
theorem root208 : Bracketed 208 boxes208 :=
  bracketed original208 (by decide +kernel) (signAt_of_signsOK signs208)

private theorem signs209 : signsOK coeffs209 69 boxes209 = true := by
  decide +kernel
theorem root209 : Bracketed 209 boxes209 :=
  bracketed original209 (by decide +kernel) (signAt_of_signsOK signs209)

private theorem signs210 : signsOK coeffs210 70 boxes210 = true := by
  decide +kernel
theorem root210 : Bracketed 210 boxes210 :=
  bracketed original210 (by decide +kernel) (signAt_of_signsOK signs210)

private theorem signs211 : signsOK coeffs211 70 boxes211 = true := by
  decide +kernel
theorem root211 : Bracketed 211 boxes211 :=
  bracketed original211 (by decide +kernel) (signAt_of_signsOK signs211)

private theorem signs212 : signsOK coeffs212 70 boxes212 = true := by
  decide +kernel
theorem root212 : Bracketed 212 boxes212 :=
  bracketed original212 (by decide +kernel) (signAt_of_signsOK signs212)

private theorem signs213 : signsOK coeffs213 71 boxes213 = true := by
  decide +kernel
theorem root213 : Bracketed 213 boxes213 :=
  bracketed original213 (by decide +kernel) (signAt_of_signsOK signs213)

private theorem signs214 : signsOK coeffs214 71 boxes214 = true := by
  decide +kernel
theorem root214 : Bracketed 214 boxes214 :=
  bracketed original214 (by decide +kernel) (signAt_of_signsOK signs214)

private theorem signs215 : signsOK coeffs215 71 boxes215 = true := by
  decide +kernel
theorem root215 : Bracketed 215 boxes215 :=
  bracketed original215 (by decide +kernel) (signAt_of_signsOK signs215)


#print axioms root215

end OrderedPartitions.ThreePoleFinite
