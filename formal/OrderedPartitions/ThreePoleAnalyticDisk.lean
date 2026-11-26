import OrderedPartitions.ThreePoleFunction
import OrderedPartitions.ThreePoleExpRemainder
import OrderedPartitions.ThreePoleDiskExistence

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Metric

theorem second_jet (q : ℝ) (c w : ℂ) :
    G q (c+w) - (G q c + first q c*w + second q c*w^2/2) =
      (q:ℂ)*Complex.exp c*(Complex.exp w-(1+w+w^2/2)) := by
  simp only [G,first,second,Complex.exp_add]
  ring

theorem second_jet_bound {q : ℝ} (hq : 0 ≤ q) (c w : ℂ) :
    ‖G q (c+w)-(G q c+first q c*w+second q c*w^2/2)‖ ≤
      q*Real.exp (c.re+‖w‖)*‖w‖^3/6 := by
  have rem := exp_remainder w 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at rem
  have rem' : ‖Complex.exp w-(1+w+w^2/2)‖ ≤ ‖w‖^3/6*Real.exp ‖w‖ := by
    exact rem
  rw [second_jet,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq,
    Complex.norm_exp,Real.exp_add]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left rem' (mul_nonneg hq (Real.exp_pos _).le)
    _ = _ := by ring

theorem parameter_bound (q q0 : ℝ) (c w : ℂ) :
    ‖G q (c+w)-G q0 (c+w)‖ ≤ |q-q0| *(2+Real.exp (c.re+‖w‖)) := by
  have factor : G q (c+w)-G q0 (c+w) = ((q-q0:ℝ):ℂ)*(Complex.exp (c+w)-2) := by
    simp only [G,Complex.ofReal_sub]; ring
  rw [factor,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have ex : ‖Complex.exp (c+w)‖ ≤ Real.exp (c.re+‖w‖) := by
    rw [Complex.norm_exp,Complex.add_re]
    exact Real.exp_le_exp.mpr (add_le_add_right (Complex.re_le_norm w) _)
  have h := norm_sub_le (Complex.exp (c+w)) (2:ℂ)
  norm_num at h
  linarith

#print axioms second_jet_bound
#print axioms parameter_bound
end OrderedPartitions.ThreePole
