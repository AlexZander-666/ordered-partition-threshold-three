import OrderedPartitions.ThreePoleFiniteData.Counts072

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs72 : signsOK coeffs72 24 boxes72 = true := by
  decide +kernel
theorem root72 : Bracketed 72 boxes72 :=
  bracketed original72 (by decide +kernel) (signAt_of_signsOK signs72)

private theorem signs73 : signsOK coeffs73 24 boxes73 = true := by
  decide +kernel
theorem root73 : Bracketed 73 boxes73 :=
  bracketed original73 (by decide +kernel) (signAt_of_signsOK signs73)

private theorem signs74 : signsOK coeffs74 24 boxes74 = true := by
  decide +kernel
theorem root74 : Bracketed 74 boxes74 :=
  bracketed original74 (by decide +kernel) (signAt_of_signsOK signs74)

private theorem signs75 : signsOK coeffs75 25 boxes75 = true := by
  decide +kernel
theorem root75 : Bracketed 75 boxes75 :=
  bracketed original75 (by decide +kernel) (signAt_of_signsOK signs75)

private theorem signs76 : signsOK coeffs76 25 boxes76 = true := by
  decide +kernel
theorem root76 : Bracketed 76 boxes76 :=
  bracketed original76 (by decide +kernel) (signAt_of_signsOK signs76)

private theorem signs77 : signsOK coeffs77 25 boxes77 = true := by
  decide +kernel
theorem root77 : Bracketed 77 boxes77 :=
  bracketed original77 (by decide +kernel) (signAt_of_signsOK signs77)

private theorem signs78 : signsOK coeffs78 26 boxes78 = true := by
  decide +kernel
theorem root78 : Bracketed 78 boxes78 :=
  bracketed original78 (by decide +kernel) (signAt_of_signsOK signs78)

private theorem signs79 : signsOK coeffs79 26 boxes79 = true := by
  decide +kernel
theorem root79 : Bracketed 79 boxes79 :=
  bracketed original79 (by decide +kernel) (signAt_of_signsOK signs79)


#print axioms root79

end OrderedPartitions.ThreePoleFinite
