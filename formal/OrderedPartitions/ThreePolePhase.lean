import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OrderedPartitions.ThreePolePhase

open Real

/-- If the additional real pole contributes a common geometric progression,
subtracting its shifted multiple of the vanishing old row removes it exactly. -/
theorem eliminate_real_mode {ψ θ u v s oldError newError newValue : ℝ}
    (old : 0 = -cos ψ + u + oldError)
    (next : newValue = -cos (ψ + θ) + s * u + newError)
    (correction : v = newError - s * oldError) :
    newValue = sin ψ * sin θ + (s - cos θ) * cos ψ + v := by
  rw [next, correction, cos_add]
  rw [show u = cos ψ - oldError by linarith]
  ring

/-- Shifted sign remains strict even when the real-mode amplitude itself is not
negligible compared with the sine of the shift. -/
theorem sign_after_elimination {ψ θ s e v : ℝ} (hθ : 0 < sin θ)
    (hc : |cos ψ| ≤ 6 / 25) (hm : |s - cos θ| ≤ (5/2 : ℝ) * sin θ)
    (he : |e| ≤ sin θ / 100)
    (hv : v = sin ψ * sin θ + (s - cos θ) * cos ψ + e) : 0 < sin ψ * v := by
  have csq : cos ψ ^ 2 ≤ (6/25 : ℝ)^2 := by
    rw [← sq_abs]
    gcongr
  have ss : (4/5 : ℝ) < |sin ψ| := by
    by_contra! h
    have low : sin ψ ^ 2 ≤ (4/5 : ℝ)^2 := by
      rw [← sq_abs]
      gcongr
    linarith [sin_sq_add_cos_sq ψ]
  have extra : |(s-cos θ)*cos ψ + e| ≤ (61/100 : ℝ) * sin θ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h := mul_le_mul hm hc (abs_nonneg _) (by positivity)
    linarith
  rcases le_or_gt (sin ψ) 0 with neg | pos
  · rw [abs_of_nonpos neg] at ss
    apply mul_pos_of_neg_of_neg (by linarith)
    linarith [(abs_le.mp extra).2, mul_lt_mul_of_pos_right (show sin ψ < -(4/5 : ℝ) by linarith) hθ]
  · rw [abs_of_pos pos] at ss
    apply mul_pos pos
    linarith [(abs_le.mp extra).1, mul_lt_mul_of_pos_right ss hθ]

#print axioms eliminate_real_mode
#print axioms sign_after_elimination

end OrderedPartitions.ThreePolePhase
