import OrderedPartitions.ThreePoleInverse
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace OrderedPartitions.ThreePole
open Filter Set Real Complex
open scoped Topology

def abscissa (r : Bool) (q y : ℝ) := branch r (q*Real.sinc y)
def path (r : Bool) (q y : ℝ) : ℂ := ⟨abscissa r q y,y⟩
def height (r : Bool) (q y : ℝ) : ℝ := (G q (path r q y)).re

private theorem good_input {q y : ℝ} (hq : 0<q) (q1 : q<1) (hy : y∈Ioo 0 Real.pi) :
    q*Real.sinc y ∈ Ioo 0 1 := by
  refine ⟨mul_pos hq ?_, (mul_le_mul_of_nonneg_left (Real.sinc_le_one y) hq.le).trans_lt (by simpa using q1)⟩
  rw [Real.sinc_of_ne_zero hy.1.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2) hy.1

theorem path_im_zero {q y : ℝ} (r : Bool) (hq : 0<q) (q1 : q<1) (hy : y∈Ioo 0 Real.pi) :
    (G q (path r q y)).im = 0 :=
  (imag_zero_iff hy.1.ne').mpr (branch_spec r (good_input hq q1 hy)).2

private theorem abscissa_diff {q y : ℝ} (r : Bool) (hq : 0<q) (q1 : q<1)
    (hy : y∈Ioo 0 Real.pi) : DifferentiableAt ℝ (abscissa r q) y := by
  have h : DifferentiableAt ℝ Real.sinc y := by
    apply ((Real.differentiableAt_sin.div differentiableAt_id hy.1.ne').congr_of_eventuallyEq _)
    filter_upwards [isOpen_ne.mem_nhds hy.1.ne'] with a an
    exact Real.sinc_of_ne_zero an
  exact (branch_deriv r (good_input hq q1 hy)).differentiableAt.comp y (h.const_mul q)

theorem height_deriv {q y : ℝ} (r : Bool) (hq : 0<q) (q1 : q<1) (hy : y∈Ioo 0 Real.pi) :
    deriv (height r q) y = -(abscissa r q y*y)*(1+(deriv (abscissa r q) y)^2) := by
  let h := deriv (abscissa r q) y
  have a := (abscissa_diff r hq q1 hy).hasDerivAt
  have pt : HasDerivAt (path r q) ((h:ℂ)+Complex.I) y := by
    have b := a.ofReal_comp.add ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I)
    rw [show path r q = fun t : ℝ ↦ ((abscissa r q t:ℝ):ℂ)+(t:ℂ)*Complex.I from
      funext (fun t ↦ (Complex.re_add_im (path r q t)).symm)]
    simpa [h] using! b
  let A := first q (path r q y)
  have dg : HasDerivAt (fun t : ℝ ↦ G q (path r q t)) (A*((h:ℂ)+Complex.I)) y := by
    simpa [A,Function.comp_def] using! ((hasDerivAt_G q (path r q y)).complexToReal_fderiv.comp_hasDerivAt y pt)
  have dr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y dg).deriv
  have di := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y dg)
  have e : (fun t : ℝ ↦ (G q (path r q t)).im) =ᶠ[𝓝 y] fun _ ↦ 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact path_im_zero r hq q1 ht
  have iz : (A*((h:ℂ)+Complex.I)).im=0 := by
    have zero := (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq e
    exact di.unique zero
  have ai : A.im=abscissa r q y*y := imaginary_curve (path_im_zero r hq q1 hy)
  change deriv (height r q) y = (A*((h:ℂ)+Complex.I)).re at dr
  rw [dr]
  simp [Complex.mul_im] at iz
  simp [Complex.mul_re]
  change A.re*h-A.im = -(abscissa r q y*y*(1+h^2))
  rw [←ai]
  nlinarith [congrArg (fun u : ℝ ↦ u*h) iz]

#print axioms height_deriv
end OrderedPartitions.ThreePole
