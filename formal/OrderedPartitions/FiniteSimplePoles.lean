import Mathlib.Analysis.Complex.RemovableSingularity

/-! Removing a finite set of simple principal parts by local divided differences. -/

noncomputable section
open Set Filter Finset
open scoped Topology
namespace OrderedPartitions.FiniteSimplePoles

def term (g : ℂ → ℂ) (a z : ℂ) : ℂ := (deriv g a)⁻¹ * (z-a)⁻¹

private def single (g : ℂ → ℂ) (a z : ℂ) : ℂ :=
  dslope (fun w : ℂ ↦ (dslope g a w)⁻¹) a z

private theorem single_eq {g : ℂ → ℂ} {a z : ℂ} (ga : g a = 0) (gz : g z ≠ 0)
    (za : z ≠ a) : single g a z = (g z)⁻¹ - term g a z := by
  simp only [single, dslope_of_ne _ za, slope_def_field, dslope_same, ga, sub_zero, term]
  field_simp [gz, sub_ne_zero.mpr za]

private theorem single_holo {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℂ}
    (da : deriv g a ≠ 0) : DifferentiableAt ℂ (single g a) a := by
  have dvd : Differentiable ℂ (dslope g a) := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (univ_mem : univ ∈ 𝓝 a)).2 hg.differentiableOn)
  let V := {z : ℂ | dslope g a z ≠ 0}
  have openV : IsOpen V := isOpen_ne_fun dvd.continuous continuous_const
  have ha : a ∈ V := by simpa [V] using da
  have invh : DifferentiableOn ℂ (fun w : ℂ ↦ (dslope g a w)⁻¹) V :=
    dvd.differentiableOn.inv fun _ hw ↦ hw
  exact ((Complex.differentiableOn_dslope (openV.mem_nhds ha)).2 invh).differentiableAt
    (openV.mem_nhds ha)

private theorem eventually_avoid (s : Finset ℂ) {c : ℂ} (hc : c ∉ s) :
    ∀ᶠ w in 𝓝 c, w ∉ s := s.finite_toSet.isClosed.isOpen_compl.mem_nhds hc

private theorem sum_holo (g : ℂ → ℂ) (s : Finset ℂ) {c : ℂ} (hc : c ∉ s) :
    DifferentiableAt ℂ (fun w ↦ ∑ a ∈ s, term g a w) c := by
  apply DifferentiableAt.fun_sum
  intro a ha
  have ne : c ≠ a := fun e ↦ hc (e ▸ ha)
  exact (differentiableAt_const ((deriv g a)⁻¹)).mul
    ((differentiableAt_id.sub_const a).inv (sub_ne_zero.mpr ne))

/-- Off finitely many simple zeros of an entire function, its reciprocal equals an
analytic remainder plus the sum of the corresponding principal parts. -/
theorem remove {g : ℂ → ℂ} (hg : Differentiable ℂ g) {U : Set ℂ} (hu : IsOpen U)
    (s : Finset ℂ) (roots : ∀ a ∈ s, g a = 0) (simple : ∀ a ∈ s, deriv g a ≠ 0)
    (exhaust : ∀ z ∈ U, g z = 0 → z ∈ s) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧
      ∀ z ∉ s, (g z)⁻¹ = H z + ∑ a ∈ s, term g a z := by
  classical
  let H (z : ℂ) := if z ∈ s then single g z z - ∑ a ∈ s.erase z, term g a z
    else (g z)⁻¹ - ∑ a ∈ s, term g a z
  refine ⟨H, fun x hx ↦ DifferentiableAt.differentiableWithinAt ?_, ?_⟩
  · by_cases hxS : x ∈ s
    · have he : x ∉ s.erase x := notMem_erase x s
      have analytic := (single_holo hg (simple x hxS)).sub (sum_holo g (s.erase x) he)
      apply analytic.congr_of_eventuallyEq
      filter_upwards [eventually_avoid (s.erase x) he, hu.mem_nhds hx] with w hw hU
      by_cases eq : w = x
      · subst w
        simp only [H, if_pos hxS, Pi.sub_apply]
      · have off : w ∉ s := fun h ↦ hw (mem_erase.mpr ⟨eq,h⟩)
        have nz : g w ≠ 0 := fun bad ↦ off (exhaust w hU bad)
        simp only [H, if_neg off, Pi.sub_apply]
        rw [single_eq (roots x hxS) nz eq, ← add_sum_erase s (fun a ↦ term g a w) hxS]
        ring
    · have nz : g x ≠ 0 := fun bad ↦ hxS (exhaust x hx bad)
      have analytic := ((hg x).inv nz).sub (sum_holo g s hxS)
      apply analytic.congr_of_eventuallyEq
      filter_upwards [eventually_avoid s hxS] with w hw
      simp [H, hw]
  · intro z hz
    simp [H, hz]

#print axioms remove
end OrderedPartitions.FiniteSimplePoles
