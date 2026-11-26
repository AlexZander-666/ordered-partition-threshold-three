import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A one-zero version of the Rouché comparison, independent of winding numbers. -/
namespace OrderedPartitions.ThreePole
open Complex Metric Set

private theorem ratio_real {p g : ℂ} (ne : g ≠ 0) (boundary : ‖g-p‖ < ‖p‖) :
    1/2 < (p/g).re := by
  have sq : ‖g-p‖^2 < ‖p‖^2 := by nlinarith [norm_nonneg (g-p)]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub] at sq
  rw [Complex.div_re, ← add_div]
  apply (lt_div_iff₀ (Complex.normSq_pos.mpr ne)).mpr
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at sq
  linarith

/-- Boundary domination of a holomorphic function by a comparison with a
center zero forces an interior zero. Multiplicities are not required. -/
theorem exists_zero_of_boundary_dominance {G P : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (gDiff : Differentiable ℂ G) (pDiff : Differentiable ℂ P)
    (zero : P c = 0) (dom : ∀ z ∈ sphere c r, ‖G z-P z‖ < ‖P z‖) :
    ∃ z ∈ ball c r, G z = 0 := by
  by_contra! no
  have nonzero : ∀ z ∈ closedBall c r, G z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with il | ed
    · exact no z (mem_ball.mpr il)
    · intro gz
      have h := dom z (mem_sphere.mpr ed)
      simp [gz] at h
  let f := fun z ↦ Complex.exp (-(P z / G z))
  have smooth : DifferentiableOn ℂ f (closedBall c r) := by
    exact Complex.differentiable_exp.comp_differentiableOn
      (pDiff.differentiableOn.div gDiff.differentiableOn nonzero).neg
  have reg : DiffContOnCl ℂ f (ball c r) :=
    ⟨smooth.mono ball_subset_closedBall, by rw [closure_ball _ hr.ne']; exact smooth.continuousOn⟩
  have edge (z) (hz : z ∈ frontier (ball c r)) : ‖f z‖ ≤ Real.exp (-(1/2)) := by
    rw [frontier_ball _ hr.ne'] at hz
    have rp := ratio_real (nonzero z (sphere_subset_closedBall hz)) (dom z hz)
    rw [show ‖f z‖ = Real.exp (-(P z/G z).re) by simp [f,Complex.norm_exp]]
    exact Real.exp_le_exp.mpr (by linarith)
  have m := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x:=c) (r:=r))
    reg edge (subset_closure (mem_ball_self hr))
  have hh : ‖f c‖ = 1 := by simp [f,zero]
  rw [hh] at m
  exact (not_lt_of_ge m) (Real.exp_lt_one_iff.mpr (by norm_num))

#print axioms exists_zero_of_boundary_dominance
end OrderedPartitions.ThreePole
