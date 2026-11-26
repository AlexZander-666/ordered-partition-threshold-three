import OrderedPartitions.ThreePoleUpperUnique
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex

/-- A convenient slope estimate on disks of imaginary height at most one. -/
theorem angular_slope {q : ℝ} {z : ℂ} (gz : G q z=0) (xp : 0≤z.re)
    (yp : 0<z.im) (y1 : z.im≤1) (rad : ‖z‖≤2) :
    ‖first q z‖ ≤ 10*Real.sin z.arg := by
  let x := z.re
  let y := z.im
  let S := Real.sin y
  let C := Real.cos y
  have ie : (G q z).im=0 := by simp [gz]
  have curve : q*Real.exp x*S=(1+x)*y := by
    simp [G,pow_two,Complex.mul_im,Complex.div_ofNat_im,Complex.exp_im] at ie
    dsimp [x,y,S]; linarith
  have re : (first q z).re = q*Real.exp x*C-(1+x) := by simp [first,C,x,y,Complex.mul_re,Complex.exp_re];ring
  have im : (first q z).im=x*y := imaginary_curve (by simp [gz])
  have yp' : 0<y := yp
  have low : y-y^3/6 ≤ S := by
    have a := (abs_le.mp (Real.abs_sub_sin_le y)).2
    rw [abs_of_pos yp'] at a; dsimp [S];linarith
  have suh : S≤y := Real.sin_le (le_of_lt yp')
  have cub : y^3 ≤ y := by
    calc
      _ = y*y*y := by ring
      _ ≤ 1*1*y := by gcongr
      _ = y := by ring
  have sp : 0<S := by linarith
  have sh : y/2≤S := by linarith
  have cl : 1-y^2/2≤C := Real.one_sub_sq_div_two_le_cos
  have cu : C≤1 := Real.cos_le_one _
  have ds : |y*C-S| ≤ y^3/2 := by
    rw [abs_le];constructor
    · nlinarith only [mul_le_mul_of_nonneg_left cl yp'.le,suh]
    · nlinarith only [mul_le_mul_of_nonneg_left cu yp'.le,low,pow_nonneg yp'.le 3]
  have pr : (first q z).re*S=(1+x)*(y*C-S) := by
    rw [re];linear_combination C*curve
  have boundRe : |(first q z).re| ≤ (1+x)*y^2 := by
    have bound : |(first q z).re| * S ≤ (1+x)*(y^3/2) := by
      rw [←abs_of_pos sp,←abs_mul,pr,abs_mul,abs_of_nonneg (show 0 ≤ 1+x by dsimp [x];linarith)]
      exact mul_le_mul_of_nonneg_left ds (by dsimp [x];linarith)
    apply le_of_mul_le_mul_right (a:=S) _ sp
    calc
      _ ≤ (1+x)*(y^3/2) := bound
      _ = ((1+x)*y^2)*(y/2) := by ring
      _ ≤ _ := by gcongr
  have xr : x≤2 := (Complex.re_le_norm z).trans rad
  have h : ‖first q z‖ ≤ 5*y := by
    have norm := Complex.norm_le_abs_re_add_abs_im (first q z)
    rw [im,abs_of_nonneg (mul_nonneg xp yp.le)] at norm
    have rp : (1+x)*y^2≤3*(1*y) := by rw [pow_two];gcongr; linarith
    have ip : x*y≤2*y := mul_le_mul_of_nonneg_right xr yp.le
    linarith
  rw [Complex.sin_arg]
  have rn : 0<‖z‖ := lt_of_lt_of_le yp (Complex.im_le_norm z)
  rw [←mul_div_assoc, le_div_iff₀ rn]
  calc
    _ ≤ (5*y)*2 := mul_le_mul h rad (norm_nonneg _) (by positivity)
    _ = 10*z.im := by dsimp [y]; ring

#print axioms angular_slope
end OrderedPartitions.ThreePole
