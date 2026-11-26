import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex
/-- The denominator after the negative-axis substitution for threshold three. -/
def G (q : ℝ) (z : ℂ) : ℂ := 1-2*(q:ℂ)-z-z^2/2+(q:ℂ)*Complex.exp z
def first (q : ℝ) (z : ℂ) : ℂ := (q:ℂ)*Complex.exp z-1-z
def second (q : ℝ) (z : ℂ) : ℂ := (q:ℂ)*Complex.exp z-1

theorem hasDerivAt_G (q : ℝ) (z : ℂ) : HasDerivAt (G q) (first q z) z := by
  have h := (((hasDerivAt_const z (1 - 2*(q:ℂ))).sub (hasDerivAt_id z)).sub
    (((hasDerivAt_id z).pow 2).div_const 2)).add ((Complex.hasDerivAt_exp z).const_mul (q:ℂ))
  unfold G first
  convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)

theorem differentiable_G (q : ℝ) : Differentiable ℂ (G q) :=
  fun z ↦ (hasDerivAt_G q z).differentiableAt

theorem first_at_root {q : ℝ} {z : ℂ} (hz : G q z = 0) :
    first q z = z^2/2 - 2*(1-(q:ℂ)) := by
  unfold G at hz
  unfold first
  linear_combination hz

theorem imaginary_curve {q : ℝ} {z : ℂ} (hy : (G q z).im = 0) :
    (first q z).im = z.re*z.im := by
  simp [G,first,pow_two,Complex.mul_im,Complex.div_ofNat_im] at hy ⊢
  linarith

#print axioms imaginary_curve
end OrderedPartitions.ThreePole
