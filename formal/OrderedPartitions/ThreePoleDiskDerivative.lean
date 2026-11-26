import OrderedPartitions.ThreePoleDiskGeometry

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open ThreePole QComplex Complex Real Metric

theorem negative_beyond {c : Cell} (hc : c∈cells) {q : ℝ} (hq : 69/100≤q)
    (q1 : q<1) (ql : (c.qLo:ℝ)≤q) (qh : q≤(c.qHi:ℝ)) :
    ∃ v : ℝ, (c.negCap:ℝ)<v ∧ v<2 ∧ G q (-(v:ℂ))=0 ∧
      0 < (c.negDeriv:ℝ) ∧ (c.negDeriv:ℝ) ≤ (first q (-(v:ℂ))).re := by
  have hg := List.all_eq_true.mp all_pass c hc
  simp only [Cell.passes,Cell.geometry,Cell.budget,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨_,_,dp,_,_,_,_,da,av,vt,_⟩ := hg.1
  have Vp : 0<(c.negCap:ℝ) := by exact_mod_cast dp.trans (da.trans av)
  have V2 : (c.negCap:ℝ)<2 := by exact_mod_cast vt
  have qp : 0<q := by linarith
  have bn : axis q (-2)<0 := by
    have expb : Real.exp (-2)<1/2 := by
      rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp 2
      norm_num at *;linarith
    rw [g_real];nlinarith [mul_lt_mul_of_pos_left expb qp]
  have bp : 0<axis q (-(c.negCap:ℝ)) := by
    simpa only [axis,Complex.ofReal_neg,Complex.ofReal_ratCast] using negative_point hc qp.le ql qh
  obtain ⟨w,win,wzero⟩ := intermediate_value_Ioo (show (-2:ℝ)≤ -(c.negCap:ℝ) by linarith)
    (axis_cont q).continuousOn (show 0∈Set.Ioo (axis q (-2)) (axis q (-(c.negCap:ℝ))) from ⟨bn,bp⟩)
  have gw : G q (w:ℂ)=0 := by
    apply Complex.ext
    · exact wzero
    · simp [G,←Complex.ofReal_exp,Complex.mul_im,pow_two]
  have re := congrArg Complex.re (first_at_root gw)
  simp [pow_two,Complex.mul_re,Complex.div_ofNat_re] at re
  refine ⟨-w,by linarith [win.2],by linarith [win.1],by simpa only [Complex.ofReal_neg,neg_neg] using gw,
    by exact_mod_cast hg.2.1,?_⟩
  simp only [Complex.ofReal_neg,neg_neg,Cell.negDeriv,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat] 
  nlinarith [mul_nonneg (show 0≤ -w-(c.negCap:ℝ) by linarith [win.2]) (show 0≤ -w+(c.negCap:ℝ) by linarith [win.2])]

theorem derivative_factor {c : Cell} (hc : c∈cells) {q : ℝ} (q1 : q<1) (ql : (c.qLo:ℝ)≤q)
    {z : ℂ} (gz : G q z=0) (hz : z∈ball (value (c.x,c.y)) (c.radius:ℝ)) (yi : 0<z.im) :
    ‖first q z‖ ≤ (c.derivCap:ℝ)*Real.sin z.arg := by
  obtain ⟨xp,y1,rad,cv,v2⟩ := disk_norm hc hz
  have sp : 0<‖z‖ := yi.trans_le (Complex.im_le_norm z)
  have capp : 0 ≤ (c.cap:ℝ) := (sp.trans rad).le
  have S : 0<Real.sin z.arg := by rw [Complex.sin_arg]; exact div_pos yi sp
  have basic := angular_slope gz xp.le yi y1 (rad.trans (cv.trans v2)).le
  have high : ‖first q z‖≤12*Real.sin z.arg := by linarith
  unfold Cell.derivCap
  split
  next cond =>
    push_cast
    rw [min_mul_of_nonneg _ _ S.le,le_min_iff]
    refine ⟨high,?_⟩
    have den : 0<(c.y:ℝ)-c.radius := by exact_mod_cast sub_pos.mpr cond
    have ybound : (c.y:ℝ)-c.radius≤z.im := by
      have rr := (abs_lt.mp ((Complex.abs_im_le_norm (z-value (c.x,c.y))).trans_lt
        (show ‖z-value (c.x,c.y)‖<(c.radius:ℝ) by simpa [dist_eq_norm] using mem_ball.mp hz))).1
      change -(c.radius:ℝ)<z.im-(c.y:ℝ) at rr
      linarith
    have abs : ‖first q z‖≤(c.cap:ℝ)^2/2+2*(1-c.qLo) := by
      rw [first_at_root gz]
      apply (norm_sub_le _ _).trans
      simp only [norm_div,norm_pow,norm_mul,Complex.norm_ofNat]
      have rr : ‖(1:ℂ)-(q:ℂ)‖=1-q := by
        rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      rw [rr];gcongr
    rw [Complex.sin_arg,←mul_div_assoc,le_div_iff₀ sp]
    rw [div_mul_eq_mul_div,le_div_iff₀ den]
    calc
      _ ≤ (‖first q z‖*(c.cap:ℝ))*z.im := by gcongr
      _ ≤ _ := by gcongr
  next => simpa using high

#print axioms derivative_factor
#print axioms negative_beyond
end OrderedPartitions.ThreePoleCert
