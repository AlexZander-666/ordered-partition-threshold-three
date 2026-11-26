import OrderedPartitions.ThreePoleUpperUnique
import OrderedPartitions.ThreePoleRectangleBound

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Set

def axis (q x : ℝ) := (G q (x:ℂ)).re

theorem g_real (q x : ℝ) : axis q x = 1-2*q-x-x^2/2+q*Real.exp x := by
  simp [axis,G,←Complex.ofReal_exp,Complex.mul_re, pow_two]

theorem axis_deriv (q x : ℝ) : HasDerivAt (axis q) (Real.exp x*(q-profile x)) x := g_real_deriv q x

theorem axis_cont (q : ℝ) : Continuous (axis q) :=
  continuous_iff_continuousAt.mpr fun x ↦ (g_real_deriv q x).continuousAt

theorem stationary_value (q x : ℝ) (eq : profile x=q) :
    axis q x = 2-2*q-x^2/2 := by
  have ex : q*Real.exp x=1+x := by rw [←eq,profile,Real.exp_neg]; field_simp
  rw [g_real,ex];ring

/-- A single sign at the positive stationary point suffices on the whole positive ray. -/
theorem positive_axis {q : ℝ} (hq : 0<q) (q1 : q<1) (osc : 0<axis q (branch true q))
    {x : ℝ} (xp : 0≤x) : 0<axis q x := by
  let a := branch true q
  obtain ⟨as,af⟩ := branch_spec true (show q∈Ioo 0 1 from ⟨hq,q1⟩)
  have ap : 0<a := as
  change profile a=q at af
  have dn : AntitoneOn (axis q) (Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) (axis_cont q).continuousOn (fun t _ ↦ (axis_deriv q t).differentiableAt.differentiableWithinAt)
    intro t ht
    have h := interior_subset ht
    have m := profile_right.antitoneOn h.1 ap.le h.2
    rw [(axis_deriv q t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (af ▸ m))
  have up : MonotoneOn (axis q) (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (axis_cont q).continuousOn (fun t _ ↦ (axis_deriv q t).differentiableAt.differentiableWithinAt)
    intro t ht
    have h : a≤t := interior_subset ht
    have m := profile_right.antitoneOn ap.le (ap.le.trans h) h
    rw [(axis_deriv q t).deriv]
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (af ▸ m))
  rcases le_total x a with sm|lg
  · exact osc.trans_le (dn ⟨xp,sm⟩ (right_mem_Icc.mpr ap.le) sm)
  · exact osc.trans_le (up (Set.mem_Ici.mpr (le_refl a)) (show x∈Ici a from lg) lg)

theorem negative_axis {q : ℝ} (hq : 69/100≤q) (q1 : q<1) :
    ∃ z ∈ Ioo (-2:ℝ) 0, G q (z:ℂ)=0 ∧ 0<(first q (z:ℂ)).re ∧
      ∀ u : ℝ, u<0 → G q (u:ℂ)=0 → u=z := by
  have qp : 0<q := by linarith
  let b := branch false q
  obtain ⟨bs,bf⟩ := branch_spec false (show q∈Ioo 0 1 from ⟨qp,q1⟩)
  have bn : b<0 := bs
  change profile b=q at bf
  have bmin : -1<b := by
    have h : 0<(1+b)*Real.exp (-b) := by change 0 < profile b; rw [bf]; exact qp
    have := pos_of_mul_pos_left h (Real.exp_pos _).le
    linarith
  have deriv_pos {t : ℝ} (lt : t<b) : 0 < Real.exp t*(q-profile t) := by
    have m := profile_left (le_trans lt.le bn.le) bn.le lt
    rw [bf] at m; exact mul_pos (Real.exp_pos _) (sub_pos.mpr m)
  have inc : StrictMonoOn (axis q) (Iic b) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic _) (axis_cont q).continuousOn
    intro t ht; rw [interior_Iic] at ht
    exact (axis_deriv q t).deriv ▸ deriv_pos ht
  have dec : AntitoneOn (axis q) (Icc b 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..) (axis_cont q).continuousOn
      (fun t _ ↦ (axis_deriv q t).differentiableAt.differentiableWithinAt)
    intro t ht
    have h := interior_subset ht
    have m := profile_left.monotoneOn bn.le h.2 h.1
    rw [(axis_deriv q t).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (bf ▸ m))
  have zpos : 0<axis q 0 := by rw [g_real]; simp; linarith
  have bpos := zpos.trans_le (dec (left_mem_Icc.mpr bn.le) (right_mem_Icc.mpr bn.le) bn.le)
  have zn : axis q (-2)<0 := by
    have expb : Real.exp (-2)<1/2 := by
      rw [Real.exp_neg,inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp 2
      norm_num at *; linarith
    rw [g_real]
    nlinarith [mul_lt_mul_of_pos_left expb qp]
  obtain ⟨z,iz,eq⟩ := intermediate_value_Ioo (show (-2:ℝ)≤b by linarith) (axis_cont q).continuousOn
    (show 0∈Ioo (axis q (-2)) (axis q b) from ⟨zn,bpos⟩)
  have real_zero : G q (z:ℂ)=0 := by
    apply Complex.ext
    · exact eq
    · simp [G,←Complex.ofReal_exp,Complex.mul_im,pow_two]
  have first_real : (first q (z:ℂ)).re=Real.exp z*(q-profile z) := by
    simp [first,profile,←Complex.ofReal_exp,Real.exp_neg,Complex.mul_re]
    field_simp; ring
  refine ⟨z,⟨iz.1,iz.2.trans bn⟩,real_zero,first_real ▸ deriv_pos iz.2,?_⟩
  intro u un gu
  have az : axis q u=0 := by simp [axis,gu]
  rcases le_total u b with l|l
  · exact inc.injOn l iz.2.le (az.trans eq.symm)
  · have pos := zpos.trans_le (dec ⟨l,un.le⟩ (right_mem_Icc.mpr bn.le) un.le)
    linarith

#print axioms negative_axis
#print axioms positive_axis
end OrderedPartitions.ThreePole
