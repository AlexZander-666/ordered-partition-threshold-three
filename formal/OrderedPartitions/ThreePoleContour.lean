import OrderedPartitions.ThreePoleRectangleBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Uniform norm bounds for the literal contour error, including the coalescence scale. -/
namespace OrderedPartitions.ThreePole
open Set Complex MeasureTheory
noncomputable section

/-- The positively oriented boundary integral, in Cartesian parametrizations. -/
def rectIntegral (f : ℂ → ℂ) : ℂ :=
  ((∫ x : ℝ in (-2)..2, f ⟨x,-Real.pi⟩) - (∫ x : ℝ in (-2)..2, f ⟨x,Real.pi⟩)) +
  I * ((∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨2,y⟩) - (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨-2,y⟩))

/-- The residual integral after extracting the origin and three principal poles. -/
def contour (q : ℝ) (n : ℕ) : ℂ :=
  rectIntegral (fun z ↦ (z^(n+1)*G q z)⁻¹) / (2*(Real.pi:ℂ)*I)

private theorem rect_norm (f : ℂ → ℂ) {c : ℝ}
    (horizontal : ∀ x : ℝ, ∀ y : ℝ, |y|=Real.pi → ‖f ⟨x,y⟩‖ ≤ c)
    (vertical : ∀ x : ℝ, |x|=2 → ∀ y : ℝ, |y|≤Real.pi → ‖f ⟨x,y⟩‖ ≤ c) :
    ‖rectIntegral f‖ ≤ (8+4*Real.pi)*c := by
  have h y (hy : |y|=Real.pi) :
      ‖∫ x : ℝ in (-2)..2, f ⟨x,y⟩‖ ≤ c*4 := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=-2) (b:=2) (fun x _ ↦ horizontal x y hy) using 1
    norm_num
  have v x (hx : |x|=2) :
      ‖∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨x,y⟩‖ ≤ c*(2*Real.pi) := by
    have e : |Real.pi - -Real.pi| = 2*Real.pi := by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy ↦ vertical x hx y ?_)).trans
    · exact le_of_eq (by rw [e])
    · rw [uIoc_of_le (by linarith [Real.pi_pos])] at hy
      exact abs_le.2 ⟨hy.1.le, hy.2⟩
  have hi := h (-Real.pi) (by simp [abs_of_pos Real.pi_pos])
  have hj := h Real.pi (abs_of_pos Real.pi_pos)
  have vi := v 2 (by norm_num)
  have vj := v (-2) (by norm_num)
  unfold rectIntegral
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith [norm_sub_le (∫ x : ℝ in (-2)..2, f ⟨x,-Real.pi⟩) (∫ x : ℝ in (-2)..2, f ⟨x,Real.pi⟩),
    norm_sub_le (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨2,y⟩) (∫ y : ℝ in (-Real.pi)..Real.pi, f ⟨-2,y⟩)]

/-- Effective bound with no external residue or complex-integral assumption. -/
theorem contour_bound {q : ℝ} (hq : 69/100≤q) (h1 : q≤1) (n : ℕ) :
    ‖contour q n‖ ≤ 36/2^(n+1) := by
  let f (z : ℂ) := (z^(n+1)*G q z)⁻¹
  have atSide (z : ℂ) (r : 2≤‖z‖)
      (side : |z.im|=Real.pi ∨ |z.re|=2 ∧ |z.im|≤Real.pi) :
      ‖f z‖ ≤ 10/2^(n+1) := by
    have g := rectangle_bound hq h1 z side
    have t := mul_le_mul (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) r (n+1)) g
      (by norm_num) (pow_nonneg (norm_nonneg z) _)
    change ‖(z^(n+1)*G q z)⁻¹‖ ≤ _
    rw [norm_inv, norm_mul, norm_pow]
    have pos : 0 < ‖z‖^(n+1)*‖G q z‖ := by positivity
    rw [inv_eq_one_div, div_le_div_iff₀ pos (by positivity)]
    linarith
  have b := rect_norm f (c:=10/2^(n+1))
    (fun x y hy ↦ atSide _ (by
      have e := Complex.abs_im_le_norm (⟨x,y⟩ : ℂ)
      change |y| ≤ _ at e
      linarith [Real.pi_gt_three]) (Or.inl hy))
    (fun x hx y hy ↦ atSide _ (by
      have e := Complex.abs_re_le_norm (⟨x,y⟩ : ℂ)
      change |x| ≤ _ at e
      linarith) (Or.inr ⟨hx,hy⟩))
  unfold contour
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real,
    norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, div_le_div_iff₀ (by positivity) (by positivity)]
  change ‖rectIntegral f‖ * _ ≤ _
  have fact : ‖rectIntegral f‖ * (2:ℝ)^(n+1) ≤ (8+4*Real.pi)*10 := by
    apply (le_div_iff₀ (by positivity)).mp
    simpa [mul_div_assoc] using b
  linarith [Real.pi_gt_three]

end
end OrderedPartitions.ThreePole
