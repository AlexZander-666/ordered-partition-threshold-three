import OrderedPartitions.ThreePoleFiniteData.Counts104

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs104 : signsOK coeffs104 34 boxes104 = true := by
  decide +kernel
theorem root104 : Bracketed 104 boxes104 :=
  bracketed original104 (by decide +kernel) (signAt_of_signsOK signs104)

private theorem signs105 : signsOK coeffs105 35 boxes105 = true := by
  decide +kernel
theorem root105 : Bracketed 105 boxes105 :=
  bracketed original105 (by decide +kernel) (signAt_of_signsOK signs105)

private theorem signs106 : signsOK coeffs106 35 boxes106 = true := by
  decide +kernel
theorem root106 : Bracketed 106 boxes106 :=
  bracketed original106 (by decide +kernel) (signAt_of_signsOK signs106)

private theorem signs107 : signsOK coeffs107 35 boxes107 = true := by
  decide +kernel
theorem root107 : Bracketed 107 boxes107 :=
  bracketed original107 (by decide +kernel) (signAt_of_signsOK signs107)

private theorem signs108 : signsOK coeffs108 36 boxes108 = true := by
  decide +kernel
theorem root108 : Bracketed 108 boxes108 :=
  bracketed original108 (by decide +kernel) (signAt_of_signsOK signs108)

private theorem signs109 : signsOK coeffs109 36 boxes109 = true := by
  decide +kernel
theorem root109 : Bracketed 109 boxes109 :=
  bracketed original109 (by decide +kernel) (signAt_of_signsOK signs109)

private theorem signs110 : signsOK coeffs110 36 boxes110 = true := by
  decide +kernel
theorem root110 : Bracketed 110 boxes110 :=
  bracketed original110 (by decide +kernel) (signAt_of_signsOK signs110)

private theorem signs111 : signsOK coeffs111 37 boxes111 = true := by
  decide +kernel
theorem root111 : Bracketed 111 boxes111 :=
  bracketed original111 (by decide +kernel) (signAt_of_signsOK signs111)


#print axioms root111

end OrderedPartitions.ThreePoleFinite
