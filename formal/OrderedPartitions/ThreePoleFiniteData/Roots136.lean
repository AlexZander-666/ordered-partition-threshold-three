import OrderedPartitions.ThreePoleFiniteData.Counts136

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs136 : signsOK coeffs136 45 boxes136 = true := by
  decide +kernel
theorem root136 : Bracketed 136 boxes136 :=
  bracketed original136 (by decide +kernel) (signAt_of_signsOK signs136)

private theorem signs137 : signsOK coeffs137 45 boxes137 = true := by
  decide +kernel
theorem root137 : Bracketed 137 boxes137 :=
  bracketed original137 (by decide +kernel) (signAt_of_signsOK signs137)

private theorem signs138 : signsOK coeffs138 46 boxes138 = true := by
  decide +kernel
theorem root138 : Bracketed 138 boxes138 :=
  bracketed original138 (by decide +kernel) (signAt_of_signsOK signs138)

private theorem signs139 : signsOK coeffs139 46 boxes139 = true := by
  decide +kernel
theorem root139 : Bracketed 139 boxes139 :=
  bracketed original139 (by decide +kernel) (signAt_of_signsOK signs139)

private theorem signs140 : signsOK coeffs140 46 boxes140 = true := by
  decide +kernel
theorem root140 : Bracketed 140 boxes140 :=
  bracketed original140 (by decide +kernel) (signAt_of_signsOK signs140)

private theorem signs141 : signsOK coeffs141 47 boxes141 = true := by
  decide +kernel
theorem root141 : Bracketed 141 boxes141 :=
  bracketed original141 (by decide +kernel) (signAt_of_signsOK signs141)

private theorem signs142 : signsOK coeffs142 47 boxes142 = true := by
  decide +kernel
theorem root142 : Bracketed 142 boxes142 :=
  bracketed original142 (by decide +kernel) (signAt_of_signsOK signs142)

private theorem signs143 : signsOK coeffs143 47 boxes143 = true := by
  decide +kernel
theorem root143 : Bracketed 143 boxes143 :=
  bracketed original143 (by decide +kernel) (signAt_of_signsOK signs143)


#print axioms root143

end OrderedPartitions.ThreePoleFinite
