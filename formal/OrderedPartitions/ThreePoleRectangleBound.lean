import OrderedPartitions.ThreePoleFunction
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit boundary separation of the three-pole denominator. -/

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex

private theorem components (q : ℝ) (z : ℂ) :
    (G q z).re = 1-2*q-z.re-(z.re^2-z.im^2)/2+
      q*Real.exp z.re*Real.cos z.im ∧
    (G q z).im = -(1+z.re)*z.im+q*Real.exp z.re*Real.sin z.im := by
  constructor <;> simp [G, pow_two, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.exp_re, Complex.exp_im] <;> ring

private theorem exp_two_low : 73/10 < Real.exp 2 := by
  rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_gt_d9, sq_nonneg (Real.exp 1-2.7)]

private theorem value_re_pos (z : ℂ) (h : 1/10 ≤ z.re) : 1/10 ≤ ‖z‖ :=
  h.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

private theorem value_re_neg (z : ℂ) (h : z.re ≤ -(1/10)) : 1/10 ≤ ‖z‖ := by
  have := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
  linarith

private theorem value_im_pos (z : ℂ) (h : 1/10 ≤ z.im) : 1/10 ≤ ‖z‖ :=
  h.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

private theorem horizontal {q : ℝ} (h1 : q ≤ 1) (x : ℝ) :
    1/10 ≤ ‖G q ⟨x, Real.pi⟩‖ := by
  have ⟨re, im⟩ := components q ⟨x, Real.pi⟩
  simp only [Real.sin_pi, Real.cos_pi, mul_zero, add_zero, mul_neg_one] at re im
  by_cases near : |1+x| < 1/10
  · obtain ⟨lo, hi⟩ := abs_lt.mp near
    have ex : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have qe : q*Real.exp x ≤ 1 := (mul_le_mul_of_nonneg_right h1
      (Real.exp_pos x).le).trans (by simpa using ex)
    apply value_re_pos
    rw [re]
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-3),
      mul_nonneg (sub_nonneg.mpr hi.le) (show 0 ≤ 1+x+1/10 by linarith)]
  · have hh := Complex.abs_im_le_norm (G q ⟨x,Real.pi⟩)
    rw [im, abs_mul, abs_neg, abs_of_pos Real.pi_pos] at hh
    have large : 1/10 ≤ |1+x| := le_of_not_gt near
    exact large.trans ((le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.pi_gt_three])).trans hh)

private theorem left_edge {q : ℝ} (hq : 69/100 ≤ q) (h1 : q ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) (hπ : y ≤ Real.pi) :
    1/10 ≤ ‖G q ⟨-2,y⟩‖ := by
  have ⟨re, im⟩ := components q ⟨-2,y⟩
  have qpos : 0 ≤ q := by linarith
  have pos : 0 ≤ q*Real.exp (-2) := mul_nonneg qpos (Real.exp_pos _).le
  by_cases large : 1/10 ≤ y
  · apply value_im_pos
    rw [im]
    nlinarith [mul_nonneg pos (Real.sin_nonneg_of_nonneg_of_le_pi hy hπ)]
  · have tiny : y < 1/10 := lt_of_not_ge large
    have expBound : Real.exp (-2) ≤ 1/7 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [exp_two_low])
    have product : q*Real.exp (-2)*Real.cos y ≤ 1/7 := by
      calc
        _ ≤ q*Real.exp (-2)*1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) pos
        _ ≤ 1*Real.exp (-2) := by rw [mul_one]; gcongr
        _ ≤ 1/7 := by simpa using expBound
    apply value_re_neg
    rw [re]
    nlinarith [mul_nonneg (sub_nonneg.mpr tiny.le) (show 0 ≤ 1/10+y by linarith)]

private theorem right_edge {q : ℝ} (hq : 69/100 ≤ q)
    {y : ℝ} (hy : 0 ≤ y) (hπ : y ≤ Real.pi) :
    1/10 ≤ ‖G q ⟨2,y⟩‖ := by
  have ⟨re, im⟩ := components q ⟨2,y⟩
  have qpos : 0 ≤ q := by linarith
  have qe : 5 ≤ q*Real.exp 2 := by
    have p := mul_le_mul hq exp_two_low.le (by norm_num : (0:ℝ) ≤ 73/10) qpos
    norm_num at p
    linarith
  have qe0 : 0 ≤ q*Real.exp 2 := by linarith
  by_cases first : y ≤ 1/5
  · have co : 49/50 ≤ Real.cos y := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := y),
        mul_nonneg (sub_nonneg.mpr first) (show 0 ≤ 1/5+y by linarith)]
    have lift := mul_le_mul_of_nonneg_left co qe0
    have low := mul_le_mul_of_nonneg_left exp_two_low.le qpos
    apply value_re_pos
    rw [re]
    nlinarith [sq_nonneg y]
  by_cases second : y ≤ 1
  · have cb : y^3 ≤ y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr second)
        (mul_nonneg hy (show 0 ≤ 1+y by linarith))]
    have si : 5/6*y ≤ Real.sin y := by nlinarith [Real.sin_ge_sub_cube hy]
    have lift := mul_le_mul qe si (by positivity : 0 ≤ 5/6*y) qe0
    apply value_im_pos
    rw [im]
    linarith
  by_cases middle : y ≤ Real.pi/2
  · have piBound : Real.pi < 16/5 := by linarith [Real.pi_lt_d2]
    have ratio : (5/8 : ℝ) ≤ 2/Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      linarith
    have si := (mul_le_mul_of_nonneg_right ratio hy).trans (Real.mul_le_sin hy middle)
    have lift := mul_le_mul qe si (by positivity : 0 ≤ 5/8*y) qe0
    apply value_im_pos
    rw [im]
    linarith
  have co0 : Real.cos y ≤ 0 := by
    have b := Real.antitoneOn_cos (show Real.pi/2 ∈ Set.Icc 0 Real.pi by
      constructor <;> linarith [Real.pi_pos]) (show y ∈ Set.Icc 0 Real.pi from ⟨hy,hπ⟩)
      (le_of_not_ge middle)
    simpa only [Real.cos_pi_div_two] using b
  by_cases fourth : y ≤ 23/10
  · apply value_re_neg
    rw [re]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos qe0 co0,
      mul_nonneg (sub_nonneg.mpr fourth) (show 0 ≤ 23/10+y by linarith)]
  · have theta : 2*(Real.pi/3) ≤ y := by linarith [Real.pi_lt_d2]
    have angle : Real.cos (2*(Real.pi/3)) = -(1/2) := by
      rw [Real.cos_two_mul, Real.cos_pi_div_three]
      norm_num
    have co := Real.antitoneOn_cos (show 2*(Real.pi/3) ∈ Set.Icc 0 Real.pi by
      constructor <;> linarith [Real.pi_pos]) (show y ∈ Set.Icc 0 Real.pi from ⟨hy,hπ⟩) theta
    rw [angle] at co
    have lift := mul_le_mul_of_nonneg_left co qe0
    have ymax : y ≤ 16/5 := by linarith [Real.pi_lt_d2]
    apply value_re_neg
    rw [re]
    nlinarith [mul_nonneg (sub_nonneg.mpr ymax) (show 0 ≤ 16/5+y by linarith)]

theorem G_conj (q : ℝ) (z : ℂ) : G q (star z) = star (G q z) := by
  simp [G, Complex.exp_conj]

/-- The full contour has a fixed clearance even at the two parameter endpoints. -/
theorem rectangle_bound {q : ℝ} (hq : 69/100 ≤ q) (h1 : q ≤ 1) (z : ℂ)
    (side : |z.im| = Real.pi ∨ |z.re| = 2 ∧ |z.im| ≤ Real.pi) :
    1/10 ≤ ‖G q z‖ := by
  have upper (w : ℂ) (pos : 0 ≤ w.im)
      (hw : |w.im| = Real.pi ∨ |w.re| = 2 ∧ |w.im| ≤ Real.pi) : 1/10 ≤ ‖G q w‖ := by
    obtain ⟨x,y⟩ := w
    change 0 ≤ y at pos
    change |y| = Real.pi ∨ |x| = 2 ∧ |y| ≤ Real.pi at hw
    rw [abs_of_nonneg pos] at hw
    rcases hw with rfl | ⟨edge, ymax⟩
    · exact horizontal h1 x
    · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 2)).mp edge with rfl | rfl
      · exact right_edge hq pos ymax
      · exact left_edge hq h1 pos ymax
  by_cases pos : 0 ≤ z.im
  · exact upper z pos side
  · have low := upper (star z) (by simpa using (le_of_not_ge pos))
      (by simpa using side)
    rw [G_conj] at low
    simpa using low

#print axioms rectangle_bound
end OrderedPartitions.ThreePole
