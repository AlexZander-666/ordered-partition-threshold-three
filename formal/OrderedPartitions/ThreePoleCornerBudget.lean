import OrderedPartitions.ThreePoleCornerPhaseBudget
import OrderedPartitions.ThreePoleCornerSlopeAngle

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Metric Set

/-- Physical pole and phase bounds in the three-way merging window. The
single condition on n*epsilon only enters the estimate for the real mode. -/
theorem corner_budget {e q : ℝ} (ep : 0<e) (eh : e≤1/32) (par : q=1-e^3/6) :
    ∃ z : ℂ, ∃ V : ℝ, G q z=0 ∧ z.im∈Ioo 0 Real.pi ∧ G q (-(V:ℂ))=0 ∧
      0<‖z‖ ∧ ‖z‖<V ∧ V<2 ∧ first q z≠0 ∧ 0<(first q (-(V:ℂ))).re ∧
      0<Real.pi/3-z.arg ∧ Real.pi/3-z.arg < (42/100)*e ∧
      |(first q z).arg-2*Real.pi/3| < (156/100)*e ∧
      (∀ n : ℕ, 1≤n → 18*‖first q z‖*(‖z‖/2)^(n+1)<e/1000) ∧
      (∀ n : ℕ, 1≤n → 3/2≤(n:ℝ)*e →
        ‖first q z‖/(2*(first q (-(V:ℂ))).re)*(‖z‖/V)^(n+1)+
           18*‖first q z‖*(‖z‖/2)^(n+1) < 6/25) ∧
      (∀ h : ℕ, 1≤h → h≤3 →
        95/100*e<Real.sin ((h:ℝ)*z.arg) ∧
        |(-(‖z‖/V))^h-Real.cos ((h:ℝ)*z.arg)| ≤ (5/2)*Real.sin ((h:ℝ)*z.arg)) := by
  subst q
  obtain ⟨v,g2,hv⟩ := negative_corner ep eh
  obtain ⟨y,hy,g1⟩ := corner_disk ep eh omega_cube
  let z := (e:ℂ)*y
  let V := e*v
  let q := 1-e^3/6
  have zp : ‖z‖=e*‖y‖ := by simp [z,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
  obtain ⟨vv,lp,lu,gap,_⟩ := corner_ratio ep eh hy hv
  obtain ⟨ypx,ypy,ap,au,_,_,_⟩ := corner_angles ep eh hy
  have argz : z.arg=y.arg := Complex.arg_real_mul _ ep
  have vn : 0<v := by linarith
  have VP : 0<V := mul_pos ep vn
  have BV : V<2 := by
    obtain ⟨_,up⟩ := abs_lt.mp hv
    have es : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
    have vl : v≤2 := by linarith
    dsimp [V];nlinarith [mul_le_mul_of_nonneg_left vl ep.le]
  have r : ‖z‖/V=‖y‖/v := by rw [zp];dsimp [V];field_simp
  have zp' : z.im>0 := by simpa [z,Complex.mul_im] using mul_pos ep ypy
  have rn := zp'.trans_le (Complex.im_le_norm z)
  have rv : ‖z‖<V := (div_lt_one VP).mp (r ▸ lu)
  have zi : z.im∈Ioo 0 Real.pi := ⟨zp',by linarith [Complex.im_le_norm z,Real.pi_gt_three]⟩
  have qp : 0<q := by
    have e2 : e^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr eh) ep.le]
    dsimp [q];nlinarith [mul_le_mul_of_nonneg_left e2 ep.le]
  have q1 : q<1 := by dsimp [q];linarith [pow_pos ep 3]
  have nz := (positive_branch_of_zero qp q1 (z:=z) g1 zi).2.2
  obtain ⟨D,_,mass,tail⟩ := corner_residues_size ep eh hy hv g1 g2
  have cr := corner_slope_angle ep eh hy g1
  have gneg : G q (-(V:ℂ))=0 := by simpa only [Complex.ofReal_neg] using g2
  refine ⟨z,V,g1,zi,gneg,rn,rv,BV,nz,D,argz ▸ ap,argz ▸ au,cr,tail,?_,?_⟩
  · intro n hn vis
    have power := corner_power ep lp gap vis
    rw [r]
    have cost := tail n hn
    change 18*‖first q z‖*(‖z‖/2)^(n+1)<e/1000 at cost
    change ‖first q z‖/(2*(first q (-(V:ℂ))).re)<522/1000 at mass
    have bound := mul_le_mul mass.le power.le (pow_nonneg lp.le (n+1)) (by norm_num)
    linarith
  · intro h hl hh
    rw [r,argz]
    exact corner_shift_factor ep eh hy hv hl hh

#print axioms corner_budget
end OrderedPartitions.ThreePole
