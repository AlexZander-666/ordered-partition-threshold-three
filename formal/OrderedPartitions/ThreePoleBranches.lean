import OrderedPartitions.ThreePoleFunction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Filter Set
open scoped Topology

def profile (x : ℝ) := (1+x)*exp (-x)

theorem profile_deriv (x : ℝ) : HasStrictDerivAt profile (-x*exp (-x)) x := by
  have h := ((hasStrictDerivAt_const x (1:ℝ)).add (hasStrictDerivAt_id x)).mul
    ((Real.hasStrictDerivAt_exp _).comp x (hasStrictDerivAt_id x).neg)
  convert h using 1 <;> first | rfl | (change -x*exp (-x) = (0+1)*exp (-x)+(1+x)*(exp (-x)*(-1)); ring)

theorem profile_left : StrictMonoOn profile (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _) (by unfold profile; fun_prop)
  intro x hx
  rw [interior_Iic] at hx
  rw [(profile_deriv x).hasDerivAt.deriv]
  exact mul_pos (neg_pos.mpr hx) (exp_pos _)

theorem profile_right : StrictAntiOn profile (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (by unfold profile; fun_prop)
  intro x hx
  rw [interior_Ici] at hx
  rw [(profile_deriv x).hasDerivAt.deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) (exp_pos _)

theorem profile_right_zero : Tendsto profile atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.add (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  change Tendsto (fun x : ℝ ↦ (1+x)*Real.exp (-x)) atTop (𝓝 0)
  simpa [add_mul] using h

theorem profile_two_branches {u : ℝ} (up : 0<u) (u1 : u<1) :
    (∃ a∈Ioo (-1:ℝ) 0, profile a=u) ∧ (∃ b∈Ioi (0:ℝ), profile b=u) := by
  have cf : Continuous profile := by unfold profile; fun_prop
  obtain ⟨b,hb⟩ := ((profile_right_zero.eventually_lt_const up).and (eventually_gt_atTop 0)).exists
  constructor
  · apply intermediate_value_Ioo (f:=profile) (by norm_num) cf.continuousOn
    simpa [profile] using And.intro up u1
  · obtain ⟨x,hx,eq⟩ := intermediate_value_Ioo' (f:=profile) hb.2.le cf.continuousOn
      (show u∈Ioo (profile b) (profile 0) from ⟨hb.1, by simpa [profile] using u1⟩)
    exact ⟨x,hx.1,eq⟩

/-- Along the real or imaginary axis, the level equation for the imaginary part is exact. -/
theorem imag_zero_iff {q x y : ℝ} (yn : y≠0) :
    (G q ⟨x,y⟩).im=0 ↔ profile x=q*Real.sinc y := by
  simp [G,pow_two,Complex.mul_im,Complex.div_ofNat_im,Complex.exp_im,profile,
    Real.sinc_of_ne_zero yn]
  have ex := Real.exp_ne_zero x
  rw [Real.exp_neg]
  field_simp
  constructor <;> intro h <;> linarith

#print axioms profile_two_branches
#print axioms imag_zero_iff
end OrderedPartitions.ThreePole
