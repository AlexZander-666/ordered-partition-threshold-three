import OrderedPartitions.ThreePoleCornerTaylor

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Metric

def cornerCenter (e : ℝ) (w : ℂ) := w-(5/12:ℂ)*(e:ℂ)*w^2

private theorem corner_poly (e : ℝ) {w : ℂ} (cw : w^3= -1) (y : ℂ) :
    cornerBase e y-3*w^2*(y-cornerCenter e w) =
    (3*w+(y-w))*(y-w)^2+(e:ℂ)*(y-w)*((y^3+y^2*w+y*w^2+w^3)/4-1) := by
  unfold cornerBase cornerCenter
  linear_combination (1-(e:ℂ)*w)*(cw)

private theorem quotient_bound {y w : ℂ} (wn : ‖w‖=1) (yn : ‖y‖ ≤ 51/50) :
    ‖(y^3+y^2*w+y*w^2+w^3)/4-1‖ ≤ 1+(51/50:ℝ)^3 := by
  have tri : ‖y^3+y^2*w+y*w^2+w^3‖ ≤ ‖y^3‖+‖y^2*w‖+‖y*w^2‖+‖w^3‖ := by
    grw [norm_add_le, norm_add_le, norm_add_le]
  simp only [norm_mul,norm_pow,wn,one_pow,mul_one] at tri
  apply (norm_sub_le _ _).trans
  norm_num [norm_div]
  have sq : ‖y‖^2 ≤ (51/50:ℝ)^2 := by gcongr
  have cu : ‖y‖^3 ≤ (51/50:ℝ)^3 := by gcongr
  linarith

theorem corner_disk {e : ℝ} (ep : 0<e) (eh : e≤1/32) {w : ℂ} (cw : w^3 = -1) :
    ∃ y∈ball (cornerCenter e w) (e^2), G (1-e^3/6) ((e:ℂ)*y)=0 := by
  have wn : ‖w‖=1 := by
    have p := congrArg norm cw
    simp only [norm_pow,norm_neg,norm_one] at p
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) (by decide : 3≠0)).mp p
  let L := fun y : ℂ ↦ 3*w^2*(y-cornerCenter e w)
  have diff : Differentiable ℂ (cornerModel e) := by
    unfold cornerModel
    have h := differentiable_G (1-e^3/6)
    fun_prop
  obtain ⟨y,hit,zero⟩ := exists_zero_of_boundary_dominance (G:=cornerModel e) (P:=L) (c:=cornerCenter e w)
    (sq_pos_of_pos ep) diff (by dsimp [L];fun_prop) (by simp [L]) (by
      intro y hy
      have ed : ‖y-cornerCenter e w‖ = e^2 := by simpa [dist_eq_norm] using mem_sphere.mp hy
      have disp : ‖cornerCenter e w-w‖=(5/12)*e := by
        unfold cornerCenter
        rw [sub_sub_cancel_left,norm_neg,norm_mul,norm_mul,norm_pow,wn]
        norm_num [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
      have eta : ‖y-w‖ ≤ (9/20)*e := by
        have hi := norm_add_le (y-cornerCenter e w) (cornerCenter e w-w)
        rw [sub_add_sub_cancel,ed,disp] at hi
        nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
      have yn : ‖y‖≤51/50 := by
        have t := norm_add_le (y-w) w
        rw [sub_add_cancel,wn] at t; linarith
      have sc : ‖3*w+(y-w)‖ ≤ 151/50 := by
        have t := norm_add_le (3*w) (y-w)
        rw [norm_mul,wn] at t;norm_num at t;linarith
      have a := quotient_bound wn yn
      have polyB : ‖cornerBase e y-L y‖ ≤ (151/50)*((9/20)*e)^2+
          e*((9/20)*e)*(1+(51/50:ℝ)^3) := by
        dsimp only [L]
        rw [corner_poly e cw]
        apply (norm_add_le _ _).trans
        simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
        gcongr
      have err := corner_tail_bound ep eh yn
      have tr := norm_add_le (cornerModel e y-cornerBase e y) (cornerBase e y-L y)
      rw [sub_add_sub_cancel] at tr
      have val : ‖L y‖ = 3*e^2 := by dsimp [L]; norm_num [norm_mul,norm_pow,wn,ed]
      rw [val]
      nlinarith only [tr,err,polyB,sq_pos_of_pos ep])
  refine ⟨y,hit,?_⟩
  exact (mul_eq_zero.mp zero).resolve_left (div_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast ep.ne')))

#print axioms corner_disk
end OrderedPartitions.ThreePole
