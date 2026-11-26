import OrderedPartitions.ThreePoleFiniteData.Counts168

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs168 : signsOK coeffs168 56 boxes168 = true := by
  decide +kernel
theorem root168 : Bracketed 168 boxes168 :=
  bracketed original168 (by decide +kernel) (signAt_of_signsOK signs168)

private theorem signs169 : signsOK coeffs169 56 boxes169 = true := by
  decide +kernel
theorem root169 : Bracketed 169 boxes169 :=
  bracketed original169 (by decide +kernel) (signAt_of_signsOK signs169)

private theorem signs170 : signsOK coeffs170 56 boxes170 = true := by
  decide +kernel
theorem root170 : Bracketed 170 boxes170 :=
  bracketed original170 (by decide +kernel) (signAt_of_signsOK signs170)

private theorem signs171 : signsOK coeffs171 57 boxes171 = true := by
  decide +kernel
theorem root171 : Bracketed 171 boxes171 :=
  bracketed original171 (by decide +kernel) (signAt_of_signsOK signs171)

private theorem signs172 : signsOK coeffs172 57 boxes172 = true := by
  decide +kernel
theorem root172 : Bracketed 172 boxes172 :=
  bracketed original172 (by decide +kernel) (signAt_of_signsOK signs172)

private theorem signs173 : signsOK coeffs173 57 boxes173 = true := by
  decide +kernel
theorem root173 : Bracketed 173 boxes173 :=
  bracketed original173 (by decide +kernel) (signAt_of_signsOK signs173)

private theorem signs174 : signsOK coeffs174 58 boxes174 = true := by
  decide +kernel
theorem root174 : Bracketed 174 boxes174 :=
  bracketed original174 (by decide +kernel) (signAt_of_signsOK signs174)

private theorem signs175 : signsOK coeffs175 58 boxes175 = true := by
  decide +kernel
theorem root175 : Bracketed 175 boxes175 :=
  bracketed original175 (by decide +kernel) (signAt_of_signsOK signs175)


#print axioms root175

end OrderedPartitions.ThreePoleFinite
