import OrderedPartitions.ThreePoleTaylor
import OrderedPartitions.ThreePoleOriginalTaylor
import OrderedPartitions.FiniteSimplePoles
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Constructions

/-! Three simple poles on the rectangle and their contributions to the original rows. -/
namespace OrderedPartitions.ThreePole
open Complex Set Filter
open scoped Topology
noncomputable section

private theorem pole_series (a A : ℂ) (an : a≠0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ A*(z-a)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ -A/a^(m+1)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (norm_pos_iff.mpr an)] with z hz
  have lt : ‖z‖<‖a‖ := by simpa using hz
  have za : z - a ≠ 0 := sub_ne_zero.mpr (fun e ↦ lt.ne (congrArg norm e))
  have small : ‖z/a‖<1 := by rw [norm_div, div_lt_one (norm_pos_iff.mpr an)]; exact lt
  convert! (hasSum_geometric_of_norm_lt_one small).mul_left (-A/a) using 1
  · ext m
    rw [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, div_pow, pow_succ]
    field_simp
  · rw [zero_add, show 1-z/a = -(z-a)/a by field_simp; ring]
    field_simp


/-- The coefficient of a reciprocal with three distinct simple poles. -/
theorem taylor_three_residues {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {U : Set ℂ} (ho : IsOpen U) (hbox : Box ⊆ U) {a b c : ℂ}
    (ar : ‖a‖<2) (br : ‖b‖<2) (cr : ‖c‖<2) (an : a≠0) (bn : b≠0) (cn : c≠0)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (ga : g a=0) (gb : g b=0) (gc : g c=0)
    (da : deriv g a≠0) (db : deriv g b≠0) (dc : deriv g c≠0)
    (onlyZeros : ∀ z∈U, g z=0 → z=a ∨ z=b ∨ z=c) (n : ℕ) :
    taylor n (fun w : ℂ ↦ (g w)⁻¹) =
      rectIntegral (fun w : ℂ ↦ (w^(n+1)*g w)⁻¹)/(2*(Real.pi:ℂ)*I) -
        (deriv g a)⁻¹/a^(n+1) - (deriv g b)⁻¹/b^(n+1) - (deriv g c)⁻¹/c^(n+1) := by
  classical
  obtain ⟨H,hH,remainder⟩ := FiniteSimplePoles.remove hg ho {a,b,c}
    (by simpa using And.intro ga ⟨gb,gc⟩) (by simpa using And.intro da ⟨db,dc⟩)
    (fun z hz zg ↦ by simpa using onlyZeros z hz zg)
  let A := (deriv g a)⁻¹
  let B := (deriv g b)⁻¹
  let C := (deriv g c)⁻¹
  let F (w : ℂ) := (g w)⁻¹
  have split (z : ℂ) (za : z≠a) (zb : z≠b) (zc : z≠c) :
      F z = H z + A*(z-a)⁻¹ + B*(z-b)⁻¹ + C*(z-c)⁻¹ := by
    simpa [F,A,B,C,FiniteSimplePoles.term,ab,ac,bc,add_assoc] using
      remainder z (by simp [za,zb,zc])
  have germ : (fun w : ℂ ↦ H w + A*(w-a)⁻¹ + B*(w-b)⁻¹ + C*(w-c)⁻¹) =ᶠ[𝓝 0] F := by
    filter_upwards [isOpen_ne.mem_nhds an.symm, isOpen_ne.mem_nhds bn.symm,
      isOpen_ne.mem_nhds cn.symm] with z za zb zc
    exact (split z za zb zc).symm
  obtain ⟨p,hp⟩ := hH.analyticAt (ho.mem_nhds (hbox box_zero))
  have hP := (((hp.add (pole_series a A an)).add (pole_series b B bn)).add
    (pole_series c C cn)).congr germ
  have coeff := taylor_of_series hP n
  change taylor n F = p.coeff n +
    (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -A/a^(m+1))).coeff n +
    (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -B/b^(m+1))).coeff n +
    (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -C/c^(m+1))).coeff n at coeff
  simp only [FormalMultilinearSeries.coeff_ofScalars, ←taylor_of_series hp n] at coeff
  let partH (w : ℂ) := H w / w^(n+1)
  let part (v R w : ℂ) := R*((w-v)⁻¹/w^(n+1))
  have cd : RegularOnBoundary partH := fun w hw ↦ (regular_of_holo ho hbox hH _ hw).div
    (continuousAt_id.pow _) (pow_ne_zero _ (boundary_ne_zero hw))
  have cp v (vr : ‖v‖<2) R : RegularOnBoundary (part v R) := fun _ h ↦
    continuousAt_const.mul ((kernel_regular vr _ h).div (continuousAt_id.pow _)
      (pow_ne_zero _ (boundary_ne_zero h)))
  have cancel v (vr : ‖v‖<2) (vn : v≠0) R : rectIntegral (part v R)=0 := by
    dsimp only [part]
    rw [rect_scale,polar_integral_zero vr vn,mul_zero]
  have eq := rect_congr (f:=fun w : ℂ ↦ (w^(n+1)*g w)⁻¹)
    (g:=fun w : ℂ ↦ partH w + part a A w + part b B w + part c C w) (fun w hw ↦ ?_)
  · have rA : RegularOnBoundary (fun w ↦ partH w + part a A w) :=
      fun w h ↦ (cd w h).add (cp a ar A w h)
    have rB : RegularOnBoundary (fun w ↦ partH w + part a A w + part b B w) :=
      fun w h ↦ (rA w h).add (cp b br B w h)
    rw [rect_add rB (cp c cr C), rect_add rA (cp b br B), rect_add cd (cp a ar A),
      cancel a ar an A, cancel b br bn B, cancel c cr cn C, add_zero, add_zero, add_zero] at eq
    change _ = rectIntegral (fun z : ℂ ↦ H z / z^(n+1)) at eq
    rw [rect_taylor ho hbox H hH n] at eq
    have pi0 : (2*(Real.pi:ℂ)*I)≠0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
    rw [eq,mul_div_cancel_right₀ _ pi0]
    simpa [F,A,B,C,sub_eq_add_neg,neg_div] using coeff
  · have za := sub_ne_zero.mp (boundary_sub_ne ar hw)
    have zb := sub_ne_zero.mp (boundary_sub_ne br hw)
    have zc := sub_ne_zero.mp (boundary_sub_ne cr hw)
    change _ = _
    rw [mul_inv_rev,show (g w)⁻¹ = _ from split w za zb zc]
    dsimp [partH,part,A,B,C]
    ring

/-- The exact three-pole formula expressed in terms of the original ordered-partition row. -/
theorem original_three_residues {q : ℝ} (h1 : q<1)
    {U : Set ℂ} (ho : IsOpen U) (hbox : Box ⊆ U) {a b c : ℂ}
    (ar : ‖a‖<2) (br : ‖b‖<2) (cr : ‖c‖<2) (an : a≠0) (bn : b≠0) (cn : c≠0)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (ga : G q a=0) (gb : G q b=0) (gc : G q c=0)
    (da : deriv (G q) a≠0) (db : deriv (G q) b≠0) (dc : deriv (G q) c≠0)
    (onlyZeros : ∀ z∈U, G q z=0 → z=a ∨ z=b ∨ z=c) (n : ℕ) :
    Complex.ofReal ((row n 3).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) =
      contour q n - (deriv (G q) a)⁻¹/a^(n+1) - (deriv (G q) b)⁻¹/b^(n+1) -
      (deriv (G q) c)⁻¹/c^(n+1) :=
  (iterate_dslope_inv_G_at_zero h1 n).symm.trans (taylor_three_residues (differentiable_G q)
    ho hbox ar br cr an bn cn ab ac bc ga gb gc da db dc onlyZeros n)

#print axioms taylor_three_residues
#print axioms original_three_residues
end
end OrderedPartitions.ThreePole
