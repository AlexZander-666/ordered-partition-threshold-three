import OrderedPartitions.ThreePoleCornerMass
import OrderedPartitions.ThreePoleCornerAngles

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Metric

theorem corner_power {e l : ℝ} {n : ℕ} (ep : 0<e) (lp : 0<l) (gap : (54/100)*e<1-l)
    (vis : 3/2 ≤ (n:ℝ)*e) : l^(n+1)<45/100 := by
  have b : l ≤ Real.exp (-(54/100)*e) := by linarith [Real.add_one_le_exp (-(54/100)*e)]
  have hpow := pow_le_pow_left₀ lp.le b (n+1)
  rw [←Real.exp_nat_mul] at hpow
  have i : ((n+1:ℕ):ℝ)*(-(54/100)*e) ≤ -(81/100) := by push_cast;nlinarith only [vis,ep]
  have expb := Real.sum_le_exp_of_nonneg (show 0≤(81/100:ℝ) by norm_num) 5
  norm_num [Finset.sum_range_succ,Nat.factorial] at expb
  apply hpow.trans_lt ((Real.exp_le_exp.mpr i).trans_lt ?_)
  rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num;linarith

theorem corner_shift_factor {e v : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) (hv : |v-(1+5*e/12)| < e^2)
    {h : ℕ} (hl : 1≤h) (hh : h≤3) :
    95/100*e<Real.sin ((h:ℝ)*y.arg) ∧
      |(-(‖y‖/v))^h-Real.cos ((h:ℝ)*y.arg)|≤(5/2)*Real.sin ((h:ℝ)*y.arg) := by
  obtain ⟨_,lp,lu,_,gap⟩ := corner_ratio ep eh hy hv
  obtain ⟨_,_,ap,au,s1,s2,s3⟩ := corner_angles ep eh hy
  let l := ‖y‖/v
  have rough (i : ℕ) (x : ℝ) : |(-l)^i-Real.cos x|≤2 := by
    apply (abs_sub _ _).trans
    have hi : |(-l)^i|≤1 := by rw [abs_pow,abs_neg,abs_of_pos lp];exact pow_le_one₀ lp.le lu.le
    linarith [Real.abs_cos_le_one x]
  interval_cases h
  · norm_num
    have rb := rough 1 y.arg; norm_num [l] at rb
    exact ⟨by linarith,by linarith⟩
  · norm_num
    have rb := rough 2 (2*y.arg); norm_num [l] at rb
    exact ⟨by linarith,by linarith⟩
  · norm_num
    refine ⟨by linarith,?_⟩
    let a := Real.pi/3-y.arg
    have rep : 3*y.arg=Real.pi-3*a := by dsimp [a];ring
    have diff : 0≤1-l^3 := sub_nonneg.mpr (pow_le_one₀ lp.le lu.le)
    have lc : 1-l^3≤3*(1-l) := by
      nlinarith [mul_nonneg (sq_nonneg (1-l)) (show 0≤l+2 from by linarith)]
    have cc := Real.one_sub_sq_div_two_le_cos (x:=3*a)
    have sq : a^2≤((42/100)*e)^2 := by gcongr
    have ee : e^2 ≤ e/32 := by nlinarith [mul_le_mul_of_nonneg_left eh ep.le]
    rw [rep,Real.cos_pi_sub]
    change |(-l)^3- -Real.cos (3*a)| ≤ _
    apply abs_le.mpr
    rw [←rep]
    constructor <;> nlinarith only [diff,lc,cc,Real.cos_le_one (3*a),sq,ee,gap,s3,ep]

#print axioms corner_shift_factor
end OrderedPartitions.ThreePole
