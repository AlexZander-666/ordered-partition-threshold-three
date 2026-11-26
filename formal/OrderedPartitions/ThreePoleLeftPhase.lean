import OrderedPartitions.ThreePoleUpperLimit
import OrderedPartitions.TwoPoleAngles

/-! The continuous arguments and the limiting phase at the double real zero. -/
noncomputable section
namespace OrderedPartitions.ThreePole
open Set Filter Complex
open scoped Topology

private theorem angle_ratio {q : ℝ} {z : ℂ} (gz : G q z=0) (xp : 0<z.re)
    (iy : z.im∈Ioo 0 (Real.pi/2)) :
    -((1+z.re)/(2*z.re))*z.im ≤ (first q z).re/(first q z).im ∧
      (first q z).re/(first q z).im ≤ 0 := by
  let x := z.re
  let y := z.im
  have x0 : 0<x := xp
  have y0 : 0<y := iy.1
  have sp : 0<Real.sin y := Real.sin_pos_of_pos_of_lt_pi y0 (by dsimp [y];linarith [iy.2,Real.pi_pos])
  have ie : (G q z).im=0 := by simp [gz]
  have curve : q*Real.exp x*Real.sin y=(1+x)*y := by
    simp [G,pow_two,Complex.mul_im,Complex.exp_im,Complex.div_ofNat_im] at ie
    dsimp [x,y];linarith
  have re : (first q z).re=(1+x)*(y*Real.cos y/Real.sin y-1) := by
    have left : (first q z).re=q*Real.exp x*Real.cos y-(1+x) := by
      simp [first,x,y,Complex.mul_re,Complex.exp_re];ring
    rw [left]
    field_simp [sp.ne']
    linear_combination Real.cos y*curve
  have im : (first q z).im=x*y := imaginary_curve (by simp [gz])
  have deficit := TwoPole.cot_deficit_bound iy
  change 0≤1-y*Real.cos y/Real.sin y ∧ 1-y*Real.cos y/Real.sin y≤y^2/2 at deficit
  change -((1+x)/(2*x))*y ≤ _ ∧ _ ≤ 0
  rw [re,im,le_div_iff₀ (mul_pos x0 y0),div_nonpos_iff]
  constructor
  · rw [show -((1+x)/(2*x))*y*(x*y)= -(1+x)*(y^2/2) by field_simp]
    nlinarith only [mul_le_mul_of_nonneg_left deficit.2 (show 0≤1+x by linarith)]
  · exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [deficit.1]),(mul_pos x0 y0).le⟩

private theorem first_cont {q : ℝ} {u : ℝ → ℂ} {s : Set ℝ} (h : ContinuousWithinAt u s q) :
    ContinuousWithinAt (fun r ↦ first r (u r)) s q := by
  unfold first
  fun_prop

theorem upper_angles_continuous {c : ℝ} (lb : 69/100≤c) (osc : ∀ q∈Ioo c 1,0<axis q (branch true q)) :
    ContinuousOn (fun q ↦ (upper q).arg) (Ioo c 1) ∧
    ContinuousOn (fun q ↦ (first q (upper q)).arg) (Ioo c 1) := by
  have data q (h : q∈Ioo c 1) := upper_spec (lb.trans h.1.le) h.2 (osc q h)
  have pos q (h : q∈Ioo c 1) : 0<(upper q).re :=
    (positive_branch_of_zero (by linarith [h.1]) h.2 (data q h).1 (data q h).2).1
  constructor
  · intro q h
    exact (Complex.continuousAt_arg (Or.inl (pos q h))).comp_continuousWithinAt (upper_continuous lb osc q h)
  · intro q h
    have im : (first q (upper q)).im=(upper q).re*(upper q).im :=
      imaginary_curve (by simp [(data q h).1])
    have non : (first q (upper q)).im≠0 := by rw [im];exact (mul_pos (pos q h) (data q h).2.1).ne'
    exact (Complex.continuousAt_arg (Or.inr non)).comp_continuousWithinAt (f:=fun r ↦ first r (upper r))
      (first_cont (upper_continuous lb osc q h))

theorem upper_angles_left {a c : ℝ} (ap : 0<a) (ci : c∈Ioo 0 1) (low : 69/100≤c)
    (level : profile a=c) (doubleRoot : c=1-a^2/4) (osc : ∀ q∈Ioo c 1,0<axis q (branch true q)) :
    Tendsto (fun q ↦ (upper q).arg) (𝓝[Ioo c 1] c) (𝓝 0) ∧
    Tendsto (fun q ↦ (first q (upper q)).arg) (𝓝[Ioo c 1] c) (𝓝 (Real.pi/2)) := by
  have upperLim := upper_critical_limit ap ci low level doubleRoot osc
  have xr : Tendsto (fun q ↦ (upper q).re) (𝓝[Ioo c 1] c) (𝓝 a) :=
    Complex.continuous_re.continuousAt.tendsto.comp upperLim
  have yi : Tendsto (fun q ↦ (upper q).im) (𝓝[Ioo c 1] c) (𝓝 0) :=
    Complex.continuous_im.continuousAt.tendsto.comp upperLim
  have dom : ∀ᶠ q in 𝓝[Ioo c 1] c,q∈Ioo c 1 := eventually_mem_nhdsWithin
  have bounds q (h : q∈Ioo c 1) := upper_spec (low.trans h.1.le) h.2 (osc q h)
  have px q (h : q∈Ioo c 1) : 0<(upper q).re :=
    (positive_branch_of_zero (ci.1.trans h.1) h.2 (bounds q h).1 (bounds q h).2).1
  have half q (h : q∈Ioo c 1) : (upper q).im∈Ioo 0 (Real.pi/2) := by
    have ex := upper_exists (low.trans h.1.le) h.2 (osc q h)
    unfold upper
    rw [dif_pos ex]
    exact ex.choose_spec.2
  constructor
  · have continuous := Complex.continuousAt_arg (x:=(a:ℂ)) (Or.inl ap)
    simpa only [Function.comp_def,Complex.arg_ofReal_of_nonneg ap.le] using continuous.tendsto.comp upperLim
  · apply TwoPole.arg_vertical_limit
    · filter_upwards [dom] with q h
      rw [imaginary_curve (show (G q (upper q)).im=0 by simp [(bounds q h).1])]
      exact mul_pos (px q h) (bounds q h).2.1
    · have lower : Tendsto (fun q ↦ -((1+(upper q).re)/(2*(upper q).re))*(upper q).im)
          (𝓝[Ioo c 1] c) (𝓝 0) := by
        simpa using (((xr.const_add 1).div (xr.const_mul 2) (by positivity)).neg.mul yi)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower tendsto_const_nhds
      · exact dom.mono (fun q h ↦ (angle_ratio (bounds q h).1 (px q h) (half q h)).1)
      · exact dom.mono (fun q h ↦ (angle_ratio (bounds q h).1 (px q h) (half q h)).2)

#print axioms upper_angles_continuous
#print axioms upper_angles_left
end OrderedPartitions.ThreePole
