import OrderedPartitions.ThreePoleRealAxis
import OrderedPartitions.ThreePoleCoveredDisks

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open ThreePole QComplex Metric Complex Set

/-- A certified disk contains the unique simple upper zero at every oscillatory
parameter of the covered window, including disks centered on the real axis. -/
theorem physical_upper {c : Cell} (hc : c∈cells) {q : ℝ} (qp : 0<q) (q1 : q<1)
    (osc : 0<axis q (branch true q)) (ql : (c.qLo:ℝ)≤q) (qh : q≤(c.qHi:ℝ)) :
    ∃ z∈ball (value (c.x,c.y)) (c.radius:ℝ), G q z=0 ∧ z.im∈Ioo 0 Real.pi ∧
      first q z≠0 ∧ ∀ w : ℂ, G q w=0 → w.im∈Ioo 0 Real.pi → w=z := by
  obtain ⟨w,win,gw⟩ := physical_disk hc ql qh
  let center := value (c.x,c.y)
  have hg := List.all_eq_true.mp all_pass c hc
  simp only [Cell.passes,Cell.geometry,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨_,_,dr,dx,yp,cone,sq,dc,cv,vt,_⟩ := hg.1
  have rad : 0<(c.radius:ℝ) := by exact_mod_cast dr
  have xs : (c.radius:ℝ) < center.re := by change (c.radius:ℝ)<c.x; exact_mod_cast dx
  have ys : 0 ≤ center.im := by change 0≤(c.y:ℝ); exact_mod_cast yp
  have n2 : ‖center‖ < (c.cap:ℝ)-c.radius := by
    have a : ‖center‖^2=(c.x:ℝ)^2+(c.y:ℝ)^2 := by simp [center,value,Complex.sq_norm,Complex.normSq_apply];ring
    have b : (c.x:ℝ)^2+(c.y:ℝ)^2<((c.cap:ℝ)-c.radius)^2 := by exact_mod_cast sq
    have dd : (c.radius:ℝ)<c.cap := by exact_mod_cast dc
    nlinarith [norm_nonneg center]
  have nw : ‖w-center‖<(c.radius:ℝ) := by simpa [dist_eq_norm] using mem_ball.mp win
  have den : 0<w.re := by
    have re := (Complex.abs_re_le_norm (w-center)).trans_lt nw
    rw [Complex.sub_re,abs_lt] at re; linarith [re.1]
  have piBound : ‖w‖<Real.pi := by
    have cap : (c.cap:ℝ)<2 := by exact_mod_cast cv.trans vt
    have tri := norm_add_le (w-center) center
    rw [sub_add_cancel] at tri
    linarith [Real.pi_gt_three]
  have nz : w.im≠0 := by
    intro eq
    have r : w=(w.re:ℂ) := by apply Complex.ext <;> simp [eq]
    have zero : axis q w.re=0 := by unfold axis; rw [←r,gw];rfl
    linarith [positive_axis qp q1 osc den.le]
  obtain ⟨z,zin,gz,iy⟩ : ∃ z∈ball center (c.radius:ℝ), G q z=0 ∧ z.im∈Ioo 0 Real.pi := by
    rcases lt_or_gt_of_ne nz with neg|pos
    · refine ⟨star w,?_,by rw [G_conj,gw,star_zero],?_,?_⟩
      · apply mem_ball.mpr
        rw [dist_eq_norm]
        have squ : ‖star w-center‖^2 ≤ ‖w-center‖^2 := by
          simp [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
          nlinarith [mul_nonpos_of_nonpos_of_nonneg neg.le ys]
        nlinarith [norm_nonneg (star w-center),norm_nonneg (w-center)]
      · simpa using neg
      · have h := (Complex.abs_im_le_norm w).trans_lt piBound
        simpa [abs_of_neg neg] using h
    · exact ⟨w,win,gw,pos,(Complex.im_le_norm w).trans_lt piBound⟩
  exact ⟨z,zin,gz,iy,(positive_branch_of_zero qp q1 gz iy).2.2,
    fun w hw iw ↦ upper_unique qp q1 hw gz iw iy⟩

#print axioms physical_upper
end OrderedPartitions.ThreePoleCert
