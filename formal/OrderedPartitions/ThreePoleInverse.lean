import OrderedPartitions.ThreePoleBranches

noncomputable section
namespace OrderedPartitions.ThreePole
open Filter Set Real
open scoped Topology

def side (r : Bool) (x : ℝ) := if r then 0<x else x<0

private theorem branch_exists (r : Bool) {u : ℝ} (h : u∈Ioo 0 1) :
    ∃ x, side r x ∧ profile x=u := by
  obtain ⟨⟨a,ha,al⟩,⟨b,hb,bl⟩⟩ := profile_two_branches h.1 h.2
  cases r
  · exact ⟨a,ha.2,al⟩
  · exact ⟨b,hb,bl⟩

def branch (r : Bool) (u : ℝ) := if h:u∈Ioo 0 1 then (branch_exists r h).choose else 0

theorem branch_spec (r : Bool) {u : ℝ} (h : u∈Ioo 0 1) :
    side r (branch r u) ∧ profile (branch r u)=u := by
  rw [branch,dif_pos h]
  exact (branch_exists r h).choose_spec

theorem side_inj {r : Bool} {a b : ℝ} (ha : side r a) (hb : side r b)
    (eq : profile a=profile b) : a=b := by
  cases r
  · exact profile_left.injOn (le_of_lt ha) (le_of_lt hb) eq
  · exact profile_right.injOn (le_of_lt ha) (le_of_lt hb) eq

theorem branch_deriv (r : Bool) {u : ℝ} (h : u∈Ioo 0 1) :
    HasDerivAt (branch r) (-branch r u*exp (-(branch r u)))⁻¹ u := by
  let x := branch r u
  obtain ⟨sx,fx⟩ := branch_spec r h
  have xn : x ≠ 0 := by cases r <;> first | exact ne_of_lt sx | exact ne_of_gt sx
  have non := mul_ne_zero (neg_ne_zero.mpr xn) (exp_ne_zero (-x))
  have os : IsOpen {y | side r y} := by cases r <;> first | exact isOpen_Iio | exact isOpen_Ioi
  have cont := (profile_deriv x).hasDerivAt.continuousAt
  have good : ∀ᶠ y in 𝓝 x, profile y∈Ioo 0 1 := by
    apply cont.eventually
    apply isOpen_Ioo.mem_nhds
    simpa [x,fx] using h
  have inv : ∀ᶠ y in 𝓝 x, branch r (profile y)=y := by
    filter_upwards [os.mem_nhds sx,good] with y sy uy
    obtain ⟨ss,ff⟩ := branch_spec r uy
    exact side_inj ss sy ff
  have derivative := ((profile_deriv x).to_local_left_inverse (f':=-x*exp (-x)) non inv).hasDerivAt
  simpa only [x,fx] using derivative

#print axioms branch_deriv
end OrderedPartitions.ThreePole
