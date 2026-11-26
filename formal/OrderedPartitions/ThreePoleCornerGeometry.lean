import OrderedPartitions.ThreePoleCornerRoots
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Real Metric
open scoped ComplexConjugate

def rot (y : ℂ) := conj omega*y

private theorem rotate_center (e : ℝ) : rot (cornerCenter e omega) = 1-(5/12:ℂ)*(e:ℂ)*omega := by
  have c : conj omega*omega=1 := by rw [←Complex.normSq_eq_conj_mul_self,←Complex.sq_norm,omega_norm];norm_num
  unfold rot cornerCenter
  linear_combination (1-(5/12:ℂ)*(e:ℂ)*omega)*c

theorem rotate_error {e : ℝ} {y : ℂ} (hy : y∈ball (cornerCenter e omega) (e^2)) :
    ‖rot y-(1-(5/12:ℂ)*(e:ℂ)*omega)‖ < e^2 := by
  have h := mem_ball.mp hy
  rw [dist_eq_norm] at h
  rw [←rotate_center,rot,rot,←mul_sub,norm_mul,Complex.norm_conj,omega_norm,one_mul]
  exact h

theorem rotated_disk_geometry {e : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) :
    1-(5/24)*e-e^2 ≤ ‖y‖ ∧ ‖y‖ ≤ 1-(5/24)*e+(1+(5/12:ℝ)^2/2)*e^2 ∧
    ‖y‖ < 1 ∧ 0<(rot y).re ∧ (32/100)*e < -(rot y).im/‖y‖ ∧
     -(rot y).im/‖y‖ < (41/100)*e := by
  let c : ℂ := 1-(5/12:ℂ)*(e:ℂ)*omega
  have rr : ‖rot y-c‖<e^2 := rotate_error hy
  have cn : ‖rot y‖=‖y‖ := by simp [rot,omega_norm]
  have re : c.re=1-5*e/24 := by dsimp [c,omega];simp [Complex.mul_re];ring
  have im : c.im= -5*Real.sqrt 3*e/24 := by dsimp [c,omega];simp [Complex.mul_im,Complex.mul_re];ring
  have er := (abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt rr))
  have ei := (abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt rr))
  rw [Complex.sub_re,re] at er
  rw [Complex.sub_im,im] at ei
  have cr : ‖c‖^2=1-5*e/12+(5/12:ℝ)^2*e^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,re,im]
    nlinarith only [congrArg (fun s : ℝ ↦ s*e^2) (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))]
  have ch : ‖c‖ ≤ 1-5*e/24+(5/12:ℝ)^2*e^2/2 := by
    nlinarith [norm_nonneg c,sq_nonneg (‖c‖-1)]
  have small : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
  have lo : 1-(5/24)*e-e^2 ≤ ‖y‖ := by
    have reNorm := Complex.re_le_norm (rot y);rw [cn] at reNorm;linarith [er.1]
  have hi : ‖y‖ ≤ 1-(5/24)*e+(1+(5/12:ℝ)^2/2)*e^2 := by
    have tri := norm_add_le (rot y-c) c
    rw [sub_add_cancel,cn] at tri;linarith
  have yn : 0<‖y‖ := by linarith
  have yu : ‖y‖<1 := by linarith
  refine ⟨lo,hi,yu,by linarith [er.1],(lt_div_iff₀ yn).mpr ?_,(div_lt_iff₀ yn).mpr ?_⟩
  · have aa := mul_lt_mul_of_pos_right s3_interval.1 ep
    nlinarith only [ei.2,aa,small,mul_lt_mul_of_pos_left yu ep,ep]
  · have aa := mul_lt_mul_of_pos_right s3_interval.2 ep
    have yl : (99/100:ℝ) ≤ ‖y‖ := by linarith
    nlinarith only [ei.1,aa,small,mul_le_mul_of_nonneg_left yl ep.le,ep]

#print axioms rotated_disk_geometry
end OrderedPartitions.ThreePole
