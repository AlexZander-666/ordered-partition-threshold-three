import OrderedPartitions.ThreePoleFiniteData.Counts144

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs144 : signsOK coeffs144 48 boxes144 = true := by
  decide +kernel
theorem root144 : Bracketed 144 boxes144 :=
  bracketed original144 (by decide +kernel) (signAt_of_signsOK signs144)

private theorem signs145 : signsOK coeffs145 48 boxes145 = true := by
  decide +kernel
theorem root145 : Bracketed 145 boxes145 :=
  bracketed original145 (by decide +kernel) (signAt_of_signsOK signs145)

private theorem signs146 : signsOK coeffs146 48 boxes146 = true := by
  decide +kernel
theorem root146 : Bracketed 146 boxes146 :=
  bracketed original146 (by decide +kernel) (signAt_of_signsOK signs146)

private theorem signs147 : signsOK coeffs147 49 boxes147 = true := by
  decide +kernel
theorem root147 : Bracketed 147 boxes147 :=
  bracketed original147 (by decide +kernel) (signAt_of_signsOK signs147)

private theorem signs148 : signsOK coeffs148 49 boxes148 = true := by
  decide +kernel
theorem root148 : Bracketed 148 boxes148 :=
  bracketed original148 (by decide +kernel) (signAt_of_signsOK signs148)

private theorem signs149 : signsOK coeffs149 49 boxes149 = true := by
  decide +kernel
theorem root149 : Bracketed 149 boxes149 :=
  bracketed original149 (by decide +kernel) (signAt_of_signsOK signs149)

private theorem signs150 : signsOK coeffs150 50 boxes150 = true := by
  decide +kernel
theorem root150 : Bracketed 150 boxes150 :=
  bracketed original150 (by decide +kernel) (signAt_of_signsOK signs150)

private theorem signs151 : signsOK coeffs151 50 boxes151 = true := by
  decide +kernel
theorem root151 : Bracketed 151 boxes151 :=
  bracketed original151 (by decide +kernel) (signAt_of_signsOK signs151)


#print axioms root151

end OrderedPartitions.ThreePoleFinite
