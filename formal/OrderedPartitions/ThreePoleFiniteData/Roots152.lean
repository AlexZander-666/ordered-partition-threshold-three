import OrderedPartitions.ThreePoleFiniteData.Counts152

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs152 : signsOK coeffs152 50 boxes152 = true := by
  decide +kernel
theorem root152 : Bracketed 152 boxes152 :=
  bracketed original152 (by decide +kernel) (signAt_of_signsOK signs152)

private theorem signs153 : signsOK coeffs153 51 boxes153 = true := by
  decide +kernel
theorem root153 : Bracketed 153 boxes153 :=
  bracketed original153 (by decide +kernel) (signAt_of_signsOK signs153)

private theorem signs154 : signsOK coeffs154 51 boxes154 = true := by
  decide +kernel
theorem root154 : Bracketed 154 boxes154 :=
  bracketed original154 (by decide +kernel) (signAt_of_signsOK signs154)

private theorem signs155 : signsOK coeffs155 51 boxes155 = true := by
  decide +kernel
theorem root155 : Bracketed 155 boxes155 :=
  bracketed original155 (by decide +kernel) (signAt_of_signsOK signs155)

private theorem signs156 : signsOK coeffs156 52 boxes156 = true := by
  decide +kernel
theorem root156 : Bracketed 156 boxes156 :=
  bracketed original156 (by decide +kernel) (signAt_of_signsOK signs156)

private theorem signs157 : signsOK coeffs157 52 boxes157 = true := by
  decide +kernel
theorem root157 : Bracketed 157 boxes157 :=
  bracketed original157 (by decide +kernel) (signAt_of_signsOK signs157)

private theorem signs158 : signsOK coeffs158 52 boxes158 = true := by
  decide +kernel
theorem root158 : Bracketed 158 boxes158 :=
  bracketed original158 (by decide +kernel) (signAt_of_signsOK signs158)

private theorem signs159 : signsOK coeffs159 53 boxes159 = true := by
  decide +kernel
theorem root159 : Bracketed 159 boxes159 :=
  bracketed original159 (by decide +kernel) (signAt_of_signsOK signs159)


#print axioms root159

end OrderedPartitions.ThreePoleFinite
