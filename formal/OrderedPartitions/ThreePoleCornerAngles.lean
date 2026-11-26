import OrderedPartitions.ThreePoleCornerGeometry

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Metric Set
open scoped ComplexConjugate

private theorem sin_test {t : ℝ} (tp : 0<t) (th : t≤1/20) :
    t*(1-(1/20)^2/6) ≤ Real.sin t := by
  have b := (abs_le.mp (Real.abs_sub_sin_le t)).2
  rw [abs_of_pos tp] at b
  have sq : t^2 ≤ (1/20:ℝ)^2 := by gcongr
  nlinarith [mul_le_mul_of_nonneg_right sq tp.le]

theorem corner_angles {e : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) :
    0 < y.re ∧ 0 < y.im ∧ 0 < Real.pi/3-y.arg ∧ Real.pi/3-y.arg < (42/100)*e ∧
    (4/5:ℝ)<Real.sin y.arg ∧ (4/5:ℝ)<Real.sin (2*y.arg) ∧
    (95/100)*e < Real.sin (3*y.arg) := by
  obtain ⟨lo,_,_,_,lb,ub⟩ := rotated_disk_geometry ep eh hy
  have small : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
  have rn : 0<‖y‖ := by linarith
  have yn := norm_pos_iff.mp rn
  have er : ‖y-omega‖ ≤ (9/20)*e := by
    have rr := mem_ball.mp hy
    rw [dist_eq_norm] at rr
    have tr := norm_add_le (y-cornerCenter e omega) (cornerCenter e omega-omega)
    rw [sub_add_sub_cancel] at tr
    have cc : ‖cornerCenter e omega-omega‖=(5/12)*e := by
      unfold cornerCenter; rw [sub_sub_cancel_left,norm_neg,norm_mul,norm_mul,norm_pow,omega_norm]
      norm_num [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    linarith
  have xr := abs_le.mp ((Complex.abs_re_le_norm (y-omega)).trans er)
  have yr := abs_le.mp ((Complex.abs_im_le_norm (y-omega)).trans er)
  simp only [Complex.sub_re,Complex.sub_im,omega] at xr yr
  have xp : 0<y.re := by linarith [xr.1]
  have yp : 0<y.im := by linarith [yr.1,s3_interval.1]
  let a := Real.pi/3-y.arg
  have ii : 0≤y.arg := Complex.arg_nonneg_iff.mpr yp.le
  have ia : y.arg<Real.pi/2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl xp)
  have aestr : a ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by dsimp [a];constructor <;> linarith [Real.pi_pos]
  have eq : Real.sin a= -(rot y).im/‖y‖ := by
    dsimp only [a];rw [Real.sin_sub,Real.sin_pi_div_three,Real.cos_pi_div_three,Complex.cos_arg yn,Complex.sin_arg]
    simp [rot,omega,Complex.mul_im];ring
  have ap : 0<a := by
    apply lt_of_not_ge
    intro no
    have bad := Real.strictMonoOn_sin.monotoneOn aestr (show (0:ℝ)∈Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos]) no
    rw [Real.sin_zero,eq] at bad;linarith
  have test := sin_test (t:=(42/100:ℝ)*e) (by positivity) (by linarith)
  have aa : a < (42/100)*e := by
    by_contra! bad
    have ss := Real.strictMonoOn_sin.monotoneOn
      (show (42/100)*e∈Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_gt_three])
      aestr bad
    rw [eq] at ss
    linarith
  have sa : 0 < Real.sin a := by rw [eq];linarith
  have au : a ≤ 1/50 := by linarith
  have cs := Real.one_sub_sq_div_two_le_cos (x:=a)
  have asq : a^2≤(1/50:ℝ)^2 := by gcongr
  have shyp : 4/5<Real.sin y.arg := by
    rw [show y.arg=Real.pi/3-a by dsimp [a];ring,Real.sin_sub,Real.sin_pi_div_three,Real.cos_pi_div_three]
    have cm : (99/100:ℝ)≤Real.cos a := by linarith
    have pos := (Real.sin_le ap.le)
    nlinarith [mul_le_mul s3_interval.1.le cm (by norm_num) (Real.sqrt_nonneg 3)]
  have shyp2 : 4/5<Real.sin (2*y.arg) := by
    rw [show 2*y.arg=Real.pi-(Real.pi/3+2*a) by dsimp [a];ring,Real.sin_pi_sub]
    have st := Real.strictMonoOn_sin.monotoneOn
      (show Real.pi/3∈Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi/3+2*a∈Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_gt_three])
      (show Real.pi/3≤Real.pi/3+2*a by linarith)
    rw [Real.sin_pi_div_three] at st;linarith [s3_interval.1]
  refine ⟨xp,yp,ap,aa,shyp,shyp2,?_⟩
  rw [show 3*y.arg=Real.pi-3*a by dsimp [a];ring,Real.sin_pi_sub,Real.sin_three_mul]
  have bound : Real.sin a ≤ 41/100*e := eq ▸ ub.le
  have close : Real.sin a ≤ 1/50 := by linarith
  have square : (Real.sin a)^2≤(1/50:ℝ)^2 := by gcongr
  have cube := mul_le_mul square bound sa.le (sq_nonneg _)
  nlinarith [cube,show (32/100)*e<Real.sin a by rw [eq];exact lb]

#print axioms corner_angles
end OrderedPartitions.ThreePole
