import OrderedPartitions.ThreePoleAnalyticDisk

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Metric

/-- A uniform linear or quadratic center comparison for an entire parameter interval. -/
theorem localize {q q0 d : ℝ} {c : ℂ} (dpos : 0 < d) (qpos : 0 ≤ q0)
    (gate : |q-q0| * (2 + Real.exp (c.re+d)) + ‖G q0 c‖ +
        ‖second q0 c‖*d^2/2 + q0*Real.exp (c.re+d)*d^3/6 < ‖first q0 c‖*d ∨
      |q-q0| * (2 + Real.exp (c.re+d)) + ‖G q0 c‖ +
        ‖first q0 c‖*d + q0*Real.exp (c.re+d)*d^3/6 < ‖second q0 c‖*d^2/2) :
    ∃ z ∈ ball c d, G q z = 0 := by
  let L (z:ℂ) := first q0 c*(z-c)
  let Q (z:ℂ) := second q0 c*(z-c)^2/2
  have estimate (z : ℂ) (hz : z ∈ sphere c d) :
      ‖G q z - (L z+Q z)‖ ≤ |q-q0| * (2+Real.exp (c.re+d)) +
          ‖G q0 c‖ + q0*Real.exp (c.re+d)*d^3/6 := by
    have nw : ‖z-c‖ = d := by simpa [dist_eq_norm] using mem_sphere.mp hz
    have jet := second_jet_bound qpos c (z-c)
    have vari := parameter_bound q q0 c (z-c)
    rw [nw,add_sub_cancel] at jet vari
    calc
      _ = ‖(G q z-G q0 z)+(G q0 z-(G q0 c+L z+Q z))+G q0 c‖ := by congr 1; ring
      _ ≤ ‖G q z-G q0 z‖ + ‖G q0 z-(G q0 c+L z+Q z)‖ + ‖G q0 c‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by dsimp [L,Q] at *; linarith
  have norms (z : ℂ) (hz : z ∈ sphere c d) :
      ‖L z‖ = ‖first q0 c‖*d ∧ ‖Q z‖ = ‖second q0 c‖*d^2/2 := by
    have nw : ‖z-c‖ = d := by simpa [dist_eq_norm] using mem_sphere.mp hz
    simp [L,Q,norm_pow,nw]
  rcases gate with h | h
  · apply exists_zero_of_boundary_dominance (P:=L) dpos (differentiable_G q)
      (by dsimp [L]; fun_prop) (by simp [L])
    intro z hz
    have tri : ‖G q z-L z‖ ≤ ‖G q z-(L z+Q z)‖+‖Q z‖ := by
      convert norm_add_le (G q z-(L z+Q z)) (Q z) using 1; congr 1; ring
    obtain ⟨l,r⟩ := norms z hz
    linarith [estimate z hz]
  · apply exists_zero_of_boundary_dominance (P:=Q) dpos (differentiable_G q)
      (by dsimp [Q]; fun_prop) (by simp [Q])
    intro z hz
    have tri : ‖G q z-Q z‖ ≤ ‖G q z-(L z+Q z)‖+‖L z‖ := by
      convert norm_add_le (G q z-(L z+Q z)) (L z) using 1; congr 1; ring
    obtain ⟨l,r⟩ := norms z hz
    linarith [estimate z hz]

#print axioms localize
end OrderedPartitions.ThreePole
