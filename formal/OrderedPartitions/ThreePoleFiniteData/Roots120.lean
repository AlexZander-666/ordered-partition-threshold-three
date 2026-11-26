import OrderedPartitions.ThreePoleFiniteData.Counts120

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs120 : signsOK coeffs120 40 boxes120 = true := by
  decide +kernel
theorem root120 : Bracketed 120 boxes120 :=
  bracketed original120 (by decide +kernel) (signAt_of_signsOK signs120)

private theorem signs121 : signsOK coeffs121 40 boxes121 = true := by
  decide +kernel
theorem root121 : Bracketed 121 boxes121 :=
  bracketed original121 (by decide +kernel) (signAt_of_signsOK signs121)

private theorem signs122 : signsOK coeffs122 40 boxes122 = true := by
  decide +kernel
theorem root122 : Bracketed 122 boxes122 :=
  bracketed original122 (by decide +kernel) (signAt_of_signsOK signs122)

private theorem signs123 : signsOK coeffs123 41 boxes123 = true := by
  decide +kernel
theorem root123 : Bracketed 123 boxes123 :=
  bracketed original123 (by decide +kernel) (signAt_of_signsOK signs123)

private theorem signs124 : signsOK coeffs124 41 boxes124 = true := by
  decide +kernel
theorem root124 : Bracketed 124 boxes124 :=
  bracketed original124 (by decide +kernel) (signAt_of_signsOK signs124)

private theorem signs125 : signsOK coeffs125 41 boxes125 = true := by
  decide +kernel
theorem root125 : Bracketed 125 boxes125 :=
  bracketed original125 (by decide +kernel) (signAt_of_signsOK signs125)

private theorem signs126 : signsOK coeffs126 42 boxes126 = true := by
  decide +kernel
theorem root126 : Bracketed 126 boxes126 :=
  bracketed original126 (by decide +kernel) (signAt_of_signsOK signs126)

private theorem signs127 : signsOK coeffs127 42 boxes127 = true := by
  decide +kernel
theorem root127 : Bracketed 127 boxes127 :=
  bracketed original127 (by decide +kernel) (signAt_of_signsOK signs127)


#print axioms root127

end OrderedPartitions.ThreePoleFinite
