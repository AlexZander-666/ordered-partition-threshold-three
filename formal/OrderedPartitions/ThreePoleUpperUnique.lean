import OrderedPartitions.ThreePoleStrip

noncomputable section
namespace OrderedPartitions.ThreePole
open Filter Set Complex Real
open scoped Topology

private theorem hcOn {q : ℝ} (r : Bool) (hq : 0<q) (q1 : q<1) :
    ContinuousOn (height r q) (Ico 0 Real.pi) := by
  intro y hy
  have u : q*Real.sinc y∈Ioo 0 1 := by
    rcases hy.1.eq_or_lt with e|yp
    · simp [←e,hq,q1]
    · refine ⟨mul_pos hq ?_,(mul_le_mul_of_nonneg_left (Real.sinc_le_one y) hq.le).trans_lt (by simpa using q1)⟩
      rw [Real.sinc_of_ne_zero yp.ne']; exact div_pos (Real.sin_pos_of_pos_of_lt_pi yp hy.2) yp
  have cc : ContinuousAt (fun t : ℝ ↦ q*Real.sinc t) y := continuousAt_const.mul Real.continuous_sinc.continuousAt
  have a : ContinuousAt (abscissa r q) y := by
    change ContinuousAt ((branch r) ∘ (fun t : ℝ ↦ q*Real.sinc t)) y
    exact ContinuousAt.comp (g:=branch r) (f:=fun t : ℝ ↦ q*Real.sinc t) (branch_deriv r u).continuousAt cc
  have pt : ContinuousAt (path r q) y := by
    rw [show path r q = fun t : ℝ ↦ ((abscissa r q t:ℝ):ℂ)+(t:ℂ)*Complex.I from
      funext (fun t ↦ (Complex.re_add_im (path r q t)).symm)]
    fun_prop
  exact (Complex.continuous_re.continuousAt.comp ((hasDerivAt_G q _).continuousAt.comp pt)).continuousWithinAt

private theorem sign_input {q y : ℝ} (hq : 0<q) (q1 : q<1) (hy : y∈Ioo 0 Real.pi) :
    q*Real.sinc y∈Ioo 0 1 := by
  refine ⟨mul_pos hq ?_,(mul_le_mul_of_nonneg_left (Real.sinc_le_one y) hq.le).trans_lt (by simpa using q1)⟩
  rw [Real.sinc_of_ne_zero hy.1.ne']; exact div_pos (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2) hy.1

theorem height_antitone {q : ℝ} (hq : 0<q) (q1 : q<1) :
    StrictAntiOn (height true q) (Ico 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico ..) (hcOn true hq q1)
  intro y hy
  rw [interior_Ico] at hy
  rw [height_deriv true hq q1 hy]
  have pa : 0 < abscissa true q y := (branch_spec true (sign_input hq q1 hy)).1
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos pa hy.1)) (by positivity)

theorem height_monotone {q : ℝ} (hq : 0<q) (q1 : q<1) :
    StrictMonoOn (height false q) (Ico 0 Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico ..) (hcOn false hq q1)
  intro y hy
  rw [interior_Ico] at hy
  rw [height_deriv false hq q1 hy]
  have pa : abscissa false q y < 0 := (branch_spec false (sign_input hq q1 hy)).1
  exact mul_pos (neg_pos.mpr (mul_neg_of_neg_of_pos pa hy.1)) (by positivity)

theorem g_real_deriv (q x : ℝ) : HasDerivAt (fun t : ℝ ↦ (G q (t:ℂ)).re)
    (Real.exp x*(q-profile x)) x := by
  have d := (hasDerivAt_G q (x:ℂ)).real_of_complex
  convert d using 1; first | rfl | (simp [first,profile,Complex.mul_re, ← Complex.ofReal_exp,Real.exp_neg]; field_simp; ring)

theorem left_initial_pos {q : ℝ} (hq : 0<q) (q1 : q<1) : 0 < height false q 0 := by
  let x := branch false q
  obtain ⟨sx,fx⟩ := branch_spec false (show q∈Ioo 0 1 from ⟨hq,q1⟩)
  have xn : x<0 := sx
  have dec : AntitoneOn (fun t : ℝ ↦ (G q (t:ℂ)).re) (Icc x 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) (fun t _ ↦ (g_real_deriv q t).continuousAt.continuousWithinAt)
    · intro t _; exact (g_real_deriv q t).differentiableAt.differentiableWithinAt
    intro t ht
    have h := interior_subset ht
    rw [(g_real_deriv q t).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have ord := profile_left.monotoneOn xn.le h.2 h.1
    change profile x=q at fx
    linarith
  have atzero := dec (left_mem_Icc.mpr xn.le) (right_mem_Icc.mpr xn.le) xn.le
  have v : (G q (0:ℂ)).re=1-q := by simp [G];ring
  have eq : path false q 0 = (x:ℂ) := by apply Complex.ext <;> simp [path,abscissa,x]
  unfold height; rw [eq]
  simp only [Complex.ofReal_zero,v] at atzero
  linarith

theorem positive_branch_of_zero {q : ℝ} (hq : 0<q) (q1 : q<1) {z : ℂ}
    (gz : G q z=0) (iy : z.im∈Ioo 0 Real.pi) :
    0<z.re ∧ z=path true q z.im ∧ first q z≠0 := by
  have im : (G q z).im=0 := by simp [gz]
  have ih : profile z.re=q*Real.sinc z.im := (imag_zero_iff iy.1.ne').mp im
  have ui := sign_input hq q1 iy
  have pz : 0<z.re := by
    rcases lt_trichotomy z.re 0 with neg|zero|pos
    · obtain ⟨bs,eq⟩ := branch_spec false ui
      have aa : z.re=abscissa false q z.im := side_inj (r:=false) neg bs (ih.trans eq.symm)
      have form : path false q z.im=z := by apply Complex.ext <;> first | exact aa.symm | rfl
      have val := height_monotone hq q1 (show (0:ℝ)∈Ico 0 Real.pi from ⟨le_rfl,Real.pi_pos⟩)
        ⟨iy.1.le,iy.2⟩ iy.1
      have hh : height false q z.im=0 := by simp [height,form,gz]
      linarith [left_initial_pos hq q1]
    · rw [zero] at ih; simp [profile] at ih; linarith [ui.2]
    · exact pos
  obtain ⟨bs,eq⟩ := branch_spec true ui
  have ar : z.re=abscissa true q z.im := side_inj (r:=true) pz bs (ih.trans eq.symm)
  refine ⟨pz,by apply Complex.ext <;> first | exact ar | rfl,?_⟩
  intro bad
  have ai := imaginary_curve im
  rw [bad,Complex.zero_im] at ai
  exact (mul_pos pz iy.1).ne' ai.symm

theorem upper_unique {q : ℝ} (hq : 0<q) (q1 : q<1) {z w : ℂ} (gz : G q z=0)
    (gw : G q w=0) (iz : z.im∈Ioo 0 Real.pi) (iw : w.im∈Ioo 0 Real.pi) : z=w := by
  have az := (positive_branch_of_zero hq q1 gz iz).2.1
  have aw := (positive_branch_of_zero hq q1 gw iw).2.1
  have hz : height true q z.im=0 := by simp [height,←az,gz]
  have hw : height true q w.im=0 := by simp [height,←aw,gw]
  have eq := (height_antitone hq q1).injOn ⟨iz.1.le,iz.2⟩ ⟨iw.1.le,iw.2⟩ (hz.trans hw.symm)
  exact az.trans ((congrArg (path true q) eq).trans aw.symm)

#print axioms upper_unique
#print axioms height_antitone
#print axioms left_initial_pos
end OrderedPartitions.ThreePole
