import OrderedPartitions.ThreePoleRealAxis
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The orbit of the positive real stationary point at the critical parameter. -/
noncomputable section
namespace OrderedPartitions.ThreePole
open Real Set

def criticalFunction (x : ℝ) := profile x-1+x^2/4

theorem critical_deriv (x : ℝ) :
    HasDerivAt criticalFunction (x*(1/2-exp (-x))) x := by
  have h := ((profile_deriv x).hasDerivAt.sub_const 1).add (((hasDerivAt_id x).pow 2).div_const 4)
  convert h using 1 <;> first | rfl | (simp only [id_eq];ring)

private theorem critical_cont : Continuous criticalFunction :=
  continuous_iff_continuousAt.mpr fun x ↦ (critical_deriv x).continuousAt

private theorem critical_signs : criticalFunction 1<0 ∧ 0<criticalFunction (11/10) := by
  have small := Real.exp_bound' (x:=(1/10:ℝ)) (by norm_num) (by norm_num) (n:=3) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at small
  have bound : exp (11/10) < 280/93 := by
    rw [show (11/10:ℝ)=1+1/10 by norm_num,exp_add]
    nlinarith [mul_le_mul_of_nonneg_left small (exp_pos 1).le,exp_one_lt_d9]
  constructor
  · unfold criticalFunction profile
    rw [exp_neg]
    field_simp
    nlinarith [exp_one_gt_d9]
  · unfold criticalFunction profile
    rw [exp_neg]
    field_simp
    nlinarith

private theorem critical_rising : StrictMonoOn criticalFunction (Ici (log 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) critical_cont.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(critical_deriv x).deriv]
  have lx : log 2 < x := hx
  have e : exp (-x)<1/2 := by
    rw [exp_neg,inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (by rw [←exp_log (by norm_num : (0:ℝ)<2)];exact exp_lt_exp.mpr lx)
  exact mul_pos (lt_trans (log_pos (by norm_num)) lx) (sub_pos.mpr e)

private theorem critical_falling : StrictAntiOn criticalFunction (Icc 0 (log 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc ..) critical_cont.continuousOn
  intro x hx
  rw [(critical_deriv x).deriv]
  have hi : x∈Ioo 0 (log 2) := by simpa only [interior_Icc] using hx
  have e : 1/2 < exp (-x) := by
    rw [exp_neg,inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (exp_pos _) (by rw [←exp_log (by norm_num : (0:ℝ)<2)];exact exp_lt_exp.mpr hi.2)
  exact mul_neg_of_pos_of_neg hi.1 (sub_neg.mpr e)

/-- A single positive critical abscissa and the oscillatory stationary sign above its level. -/
theorem critical_exists :
    ∃ a∈Ioo (1:ℝ) (11/10), criticalFunction a=0 ∧ profile a = 1-a^2/4 ∧
      (69/100:ℝ)<profile a ∧ profile a<1 ∧
      ∀ q∈Ioo (profile a) 1, 0<axis q (branch true q) := by
  obtain ⟨a,ha,ae⟩ := intermediate_value_Ioo (f:=criticalFunction)
    (by norm_num : (1:ℝ)≤11/10) critical_cont.continuousOn
    (show 0∈Ioo (criticalFunction 1) (criticalFunction (11/10)) from critical_signs)
  have id : profile a=1-a^2/4 := by unfold criticalFunction at ae;linarith
  have bound : (69/100:ℝ)<profile a := by rw [id]; nlinarith [ha.1,ha.2,sq_nonneg (a-1),mul_pos (sub_pos.mpr ha.2) (show 0<11/10+a by linarith [ha.1])]
  refine ⟨a,ha,ae,id,bound,by rw [id];nlinarith [ha.1,sq_nonneg (a-1)],?_⟩
  intro q hq
  let x := branch true q
  obtain ⟨hx,px⟩ := branch_spec true (show q∈Ioo 0 1 from ⟨by linarith [hq.1],hq.2⟩)
  change 0<x at hx
  change profile x=q at px
  have xa : x<a := by
    by_contra! h
    have le := profile_right.antitoneOn (show a∈Ici 0 from le_trans (by norm_num : (0:ℝ)≤1) ha.1.le) hx.le h
    linarith [hq.1]
  have jneg : criticalFunction x < 0 := by
    by_cases xl : x≤log 2
    · have zero : criticalFunction 0=0 := by norm_num [criticalFunction,profile]
      exact (critical_falling ⟨le_rfl,(log_pos (by norm_num)).le⟩ ⟨hx.le,xl⟩ hx).trans_eq zero
    · exact (critical_rising (le_of_not_ge xl) (le_trans (le_of_not_ge xl) xa.le) xa).trans_eq ae
  rw [stationary_value q x px]
  unfold criticalFunction at jneg
  linarith

#print axioms critical_exists
end OrderedPartitions.ThreePole
