import OrderedPartitions.ThreePoleFiniteData.Counts024

namespace OrderedPartitions.ThreePoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs24 : signsOK coeffs24 8 boxes24 = true := by
  decide +kernel
theorem root24 : Bracketed 24 boxes24 :=
  bracketed original24 (by decide +kernel) (signAt_of_signsOK signs24)

private theorem signs25 : signsOK coeffs25 8 boxes25 = true := by
  decide +kernel
theorem root25 : Bracketed 25 boxes25 :=
  bracketed original25 (by decide +kernel) (signAt_of_signsOK signs25)

private theorem signs26 : signsOK coeffs26 8 boxes26 = true := by
  decide +kernel
theorem root26 : Bracketed 26 boxes26 :=
  bracketed original26 (by decide +kernel) (signAt_of_signsOK signs26)

private theorem signs27 : signsOK coeffs27 9 boxes27 = true := by
  decide +kernel
theorem root27 : Bracketed 27 boxes27 :=
  bracketed original27 (by decide +kernel) (signAt_of_signsOK signs27)

private theorem signs28 : signsOK coeffs28 9 boxes28 = true := by
  decide +kernel
theorem root28 : Bracketed 28 boxes28 :=
  bracketed original28 (by decide +kernel) (signAt_of_signsOK signs28)

private theorem signs29 : signsOK coeffs29 9 boxes29 = true := by
  decide +kernel
theorem root29 : Bracketed 29 boxes29 :=
  bracketed original29 (by decide +kernel) (signAt_of_signsOK signs29)

private theorem signs30 : signsOK coeffs30 10 boxes30 = true := by
  decide +kernel
theorem root30 : Bracketed 30 boxes30 :=
  bracketed original30 (by decide +kernel) (signAt_of_signsOK signs30)

private theorem signs31 : signsOK coeffs31 10 boxes31 = true := by
  decide +kernel
theorem root31 : Bracketed 31 boxes31 :=
  bracketed original31 (by decide +kernel) (signAt_of_signsOK signs31)


#print axioms root31

end OrderedPartitions.ThreePoleFinite
