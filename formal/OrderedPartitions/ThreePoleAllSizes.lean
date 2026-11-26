import OrderedPartitions.ThreePoleParameters
import OrderedPartitions.ThreePoleLeftPhase
import OrderedPartitions.ThreePoleActualSigns
import OrderedPartitions.ThreePoleCornerEndpoint
import OrderedPartitions.ThreePoleFiniteVerified

/-! Pairwise interlacing of four consecutive original rows at threshold three. -/

noncomputable section

namespace OrderedPartitions.ThreePole

open Filter Polynomial RootTracking Set
open scoped Topology

/-- The original rows compared at any of the three gaps in the analytic range. -/
theorem original_analytic {n h : ℕ} (hn : 240 ≤ n) (hl : 1 ≤ h) (hh : h ≤ 3) :
    OrderedPair (n/3) (row n 3) (row (n+h) 3) := by
  obtain ⟨a, ha, _, hlevel, hcl, hc1, osc⟩ := critical_exists
  let c := profile a
  let u := stopParameter n
  let ψ := fun q : ℝ ↦ phase n q (upper q)
  have cap : (279/400:ℝ) < c ∧ c < 3/4 := critical_window ha hlevel
  have stop := stop_window hn
  have cu : c < u := cap.2.trans stop.1
  have ci : c ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hcl], hc1⟩
  obtain ⟨θcont, βcont⟩ := upper_angles_continuous hcl.le osc
  have cont : ContinuousOn ψ (Ioo c 1) := (continuousOn_const.mul θcont).add βcont
  obtain ⟨θlim, βlim⟩ := upper_angles_left (by linarith [ha.1] : 0 < a)
    ci hcl.le (show profile a = c from rfl) hlevel osc
  have phase_lim : Tendsto ψ (𝓝[Ioo c 1] c) (𝓝 (Real.pi/2)) := by
    simpa only [ψ, phase, mul_zero, zero_add] using (θlim.const_mul ((n+1:ℕ):ℝ)).add βlim
  have nhds_ne : (𝓝[Ioo c 1] c).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo hc1.ne]
    exact ⟨le_rfl,hc1.le⟩
  have below_stop : ∀ᶠ q in 𝓝[Ioo c 1] c, q < u := nhdsWithin_le_nhds (gt_mem_nhds cu)
  have in_domain : ∀ᶠ q in 𝓝[Ioo c 1] c, q ∈ Ioo c 1 := eventually_mem_nhdsWithin
  have low_phase := phase_lim.eventually (gt_mem_nhds
    (show Real.pi/2 < Real.pi+Real.pi/4 by linarith [Real.pi_pos]))
  obtain ⟨l, ldom, lu, back⟩ := (in_domain.and (below_stop.and low_phase)).exists
  have closed : Icc l u ⊆ Ioo c 1 := Icc_subset_Ioo ldom.1 stop.2
  have front : ((n/3:ℕ):ℝ)*Real.pi+(Real.pi-Real.pi/4) < ψ u := endpoint_phase hn
  have point (q : ℝ) (hq : q ∈ Icc l u) :
      0 < rowScale n q (upper q) ∧
      |rowScale n q (upper q)*(row n 3).eval (-q/(1-q))+Real.cos (ψ q)| ≤ 2/5 ∧
      ((row n 3).eval (-q/(1-q)) = 0 →
        0 < Real.sin (ψ q)*(row (n+h) 3).eval (-q/(1-q))) := by
    obtain ⟨e, ep, etop, par, visible⟩ :=
      interval_scale hn (cap.1.trans (closed hq).1).le hq.2
    exact actual_pointwise hn hl hh ep etop par visible (hcl.trans (closed hq).1).le
      (closed hq).2 (osc q (closed hq))
  obtain ⟨dp, _, pos⟩ := original_shape n
  obtain ⟨dP, lc, at_zero⟩ := original_shape (n+h)
  have pne : row n 3 ≠ 0 := fun he ↦ pos.ne' (by simp [he])
  have degrees : (row (n+h) 3).natDegree = n/3 ∨ (row (n+h) 3).natDegree = n/3+1 := by
    rw [dP]
    omega
  apply ordered_pair_on_parameter dp pne degrees lc at_zero (ci.1.trans ldom.1) lu stop.2
    (cont.mono closed) front back
  · intro q hq
    obtain ⟨posScale, err, _⟩ := point q hq
    refine ⟨rowScale n q (upper q), _ , posScale, err, ?_⟩
    unfold TwoPolePhase.negativeAxis
    ring
  · intro q hq hz
    exact (point q hq).2.2 hz

/-- For all sizes including the empty rows, each gap of at most three in
the original ordered-partition family at threshold three strictly interlaces. -/
theorem original_all (n h : ℕ) (hl : 1 ≤ h) (hh : h ≤ 3) :
    OrderedPair (n/3) (row n 3) (row (n+h) 3) := by
  by_cases hn : 240 ≤ n
  · exact original_analytic hn hl hh
  · exact ThreePoleFinite.original_finite n h (by omega) hl hh

/-- The rows at ranks `n` through `n+3` interlace pairwise. -/
theorem original_four_rows (n : ℕ) (i j : Fin 4) (hij : i < j) :
    OrderedPair ((n+i.val)/3) (row (n+i.val) 3) (row (n+j.val) 3) := by
  have lt : i.val < j.val := hij
  have upper := j.isLt
  have second : n+i.val+(j.val-i.val) = n+j.val := by omega
  simpa only [second] using original_all (n+i.val) (j.val-i.val) (by omega) (by omega)

#print axioms original_analytic
#print axioms original_all
#print axioms original_four_rows

end OrderedPartitions.ThreePole
