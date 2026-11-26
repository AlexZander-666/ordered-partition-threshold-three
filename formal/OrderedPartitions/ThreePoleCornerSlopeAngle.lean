import OrderedPartitions.ThreePoleCornerAngles
import OrderedPartitions.ThreePoleCornerMass

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Metric Set

private theorem small_arg {e : ℝ} (ep : 0<e) (eh : e≤1/32) {w : ℂ}
    (hw : ‖w-1‖≤(69/100)*e) : |w.arg| < (72/100)*e := by
  have re := (Complex.abs_re_le_norm (w-1)).trans hw
  have im := (Complex.abs_im_le_norm (w-1)).trans hw
  simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero] at re im
  have wp : 0<w.re := by linarith [(abs_le.mp re).1]
  have ar := Complex.abs_arg_le_pi_div_two_iff.mpr wp.le
  have nr : (39/40:ℝ) < ‖w‖ := by linarith [(abs_le.mp re).1,Complex.re_le_norm w]
  have t : 0< (72/100)*e := by positivity
  have limit : (72/100)*e ≤ 1/20 := by linarith
  have b := (abs_le.mp (Real.abs_sub_sin_le ((72/100)*e))).2
  rw [abs_of_pos t] at b
  have sq : ((72/100)*e)^2 ≤ (1/20:ℝ)^2 := by gcongr
  have lb : (71/100)*e < Real.sin ((72/100)*e) := by
    nlinarith [mul_le_mul_of_nonneg_right sq t.le]
  have sa : Real.sin |w.arg| = |w.im|/‖w‖ := by
    rcases le_or_gt 0 w.arg with p | p
    · rw [abs_of_nonneg p,Complex.sin_arg,abs_of_nonneg (Complex.arg_nonneg_iff.mp p)]
    · rw [abs_of_neg p,Real.sin_neg,Complex.sin_arg,abs_of_neg (Complex.arg_neg_iff.mp p)];ring
  have sml : Real.sin |w.arg| < (71/100)*e := by
    rw [sa,div_lt_iff₀ (by linarith)]
    nlinarith [mul_lt_mul_of_pos_left nr ep]
  by_contra! no
  have s := Real.strictMonoOn_sin.monotoneOn
    (show (72/100)*e∈Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_gt_three])
    (show |w.arg|∈Icc (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [abs_nonneg w.arg,Real.pi_pos],ar⟩) no
  linarith

theorem corner_slope_angle {e : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) (gz : G (1-e^3/6) ((e:ℂ)*y)=0) :
    |(first (1-e^3/6) ((e:ℂ)*y)).arg-2*Real.pi/3| < (156/100)*e := by
  let z := (e:ℂ)*y
  let w := 1-((2/3:ℂ)*e)/y^2
  obtain ⟨ulo,_,_,_,_,_⟩ := rotated_disk_geometry ep eh hy
  obtain ⟨_,yp,ap,au,_,_,_⟩ := corner_angles ep eh hy
  have es : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
  have nr : (99/100:ℝ)<‖y‖ := by linarith
  have nn : y≠0 := norm_pos_iff.mp (by linarith)
  have en : (e:ℂ)≠0 := by exact_mod_cast ep.ne'
  have zn : z≠0 := mul_ne_zero en nn
  have pert : ‖w-1‖≤(69/100)*e := by
    unfold w
    rw [sub_sub_cancel_left,norm_neg,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    norm_num [norm_div,Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity)).mpr
    have sq : (99/100:ℝ)^2≤‖y‖^2 := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left sq ep.le]
  have aw := small_arg ep eh pert
  have wn : w≠0 := by intro eq;rw [eq] at pert;norm_num at pert;linarith
  have ay : 0≤y.arg := Complex.arg_nonneg_iff.mpr yp.le
  have eqz : z.arg=y.arg := Complex.arg_real_mul _ ep
  have square : (z^2).arg=2*y.arg := by
    rw [pow_two,Complex.arg_mul zn zn (by rw [eqz];constructor <;> linarith [Real.pi_pos]),eqz,two_mul]
  have factor : first (1-e^3/6) z=(1/2:ℝ)*((z^2)*w) := by
    rw [first_at_root gz]
    dsimp [z,w];push_cast;field_simp;ring
  rw [show (e:ℂ)*y=z from rfl,factor,Complex.arg_real_mul _ (by norm_num : (0:ℝ)<1/2)]
  rw [Complex.arg_mul (pow_ne_zero 2 zn) wn (by
    rw [square];constructor <;> linarith [Real.pi_gt_three,(abs_lt.mp aw).1,(abs_lt.mp aw).2]),square]
  apply abs_lt.mpr
  constructor <;> linarith [(abs_lt.mp aw).1,(abs_lt.mp aw).2]

#print axioms corner_slope_angle
end OrderedPartitions.ThreePole
