import OrderedPartitions.ThreePoleUpperBranch

/-! Monotone height inversion and limits at a double real pole. -/
noncomputable section
namespace OrderedPartitions.ThreePole
open Set Filter Complex
open scoped Topology

theorem height_zero_limit {ι : Type*} {l : Filter ι} {Q Y : ι → ℝ} {c t : ℝ}
    (qlim : Tendsto Q l (𝓝 c)) (ci : c∈Ioo 0 1) (ti : t∈Ico 0 Real.pi)
    (ht : height true c t=0)
    (roots : ∀ᶠ i in l, Q i∈Ioo 0 1 ∧ Y i∈Ico 0 Real.pi ∧ height true (Q i) (Y i)=0) :
    Tendsto Y l (𝓝 t) := by
  apply tendsto_order.mpr
  constructor
  · intro a below
    rcases lt_or_ge a 0 with neg|pos
    · exact roots.mono (fun i hi ↦ neg.trans_le hi.2.1.1)
    have ai : a∈Ico 0 Real.pi := ⟨pos,below.trans ti.2⟩
    have sign := height_antitone ci.1 ci.2 ai ti below
    rw [ht] at sign
    filter_upwards [roots,(height_limit qlim tendsto_const_nhds ci ai).eventually_const_lt sign]
      with i hi posval
    apply ((height_antitone hi.1.1 hi.1.2).lt_iff_gt hi.2.1 ai).mp
    simpa only [hi.2.2] using posval
  · intro b above
    rcases lt_or_ge b Real.pi with small|large
    · have bi : b∈Ico 0 Real.pi := ⟨ti.1.trans above.le,small⟩
      have sign := height_antitone ci.1 ci.2 ti bi above
      rw [ht] at sign
      filter_upwards [roots,(height_limit qlim tendsto_const_nhds ci bi).eventually_lt_const sign]
        with i hi negval
      apply ((height_antitone hi.1.1 hi.1.2).lt_iff_gt bi hi.2.1).mp
      simpa only [hi.2.2] using negval
    · exact roots.mono (fun i hi ↦ hi.2.1.2.trans_le large)

private theorem root_on_path {q : ℝ} (hq : 69/100≤q) (q1 : q<1) (osc : 0<axis q (branch true q)) :
    upper q=path true q (upper q).im ∧ height true q (upper q).im=0 := by
  obtain ⟨g,i⟩ := upper_spec hq q1 osc
  have onp := (positive_branch_of_zero (by linarith) q1 g i).2.1
  exact ⟨onp,by rw [height,←onp,g];rfl⟩

theorem upper_continuous {c : ℝ} (lb : 69/100≤c)
    (osc : ∀ q∈Ioo c 1, 0<axis q (branch true q)) :
    ContinuousOn upper (Ioo c 1) := by
  intro q hq
  have dom : ∀ᶠ s in 𝓝[Ioo c 1] q, s∈Ioo c 1 := eventually_mem_nhdsWithin
  have data s (hs : s∈Ioo c 1) := upper_spec (lb.trans hs.1.le) hs.2 (osc s hs)
  have pathEq s (hs : s∈Ioo c 1) := root_on_path (lb.trans hs.1.le) hs.2 (osc s hs)
  have qlim : Tendsto id (𝓝[Ioo c 1] q) (𝓝 q) := continuousWithinAt_id.tendsto
  have ci : q∈Ioo 0 1 := ⟨by linarith [hq.1],hq.2⟩
  have yi : (upper q).im∈Ico 0 Real.pi := ⟨(data q hq).2.1.le,(data q hq).2.2⟩
  have ylim := height_zero_limit (Y:=fun s ↦ (upper s).im) qlim ci yi (pathEq q hq).2
    (dom.mono (fun s hs ↦ ⟨⟨by change 0<s;linarith [hs.1],hs.2⟩,
      ⟨(data s hs).2.1.le,(data s hs).2.2⟩,(pathEq s hs).2⟩))
  have pp := path_limit qlim ylim ci yi
  rw [←(pathEq q hq).1] at pp
  exact pp.congr' (dom.mono (fun s hs ↦ (pathEq s hs).1.symm))

theorem upper_critical_limit {a c : ℝ} (ap : 0<a) (ci : c∈Ioo 0 1) (low : 69/100≤c)
    (level : profile a=c) (doubleRoot : c=1-a^2/4)
    (osc : ∀ q∈Ioo c 1, 0<axis q (branch true q)) :
    Tendsto upper (𝓝[Ioo c 1] c) (𝓝 (a:ℂ)) := by
  have beq : branch true c=a := side_inj (r:=true) (branch_spec true ci).1 ap
    ((branch_spec true ci).2.trans level.symm)
  have p0 : path true c 0=(a:ℂ) := by
    apply Complex.ext <;> simp [path,abscissa,beq]
  have h0 : height true c 0=0 := by
    rw [height,p0]
    change axis c a=0
    rw [stationary_value c a level]
    linarith
  have dom : ∀ᶠ s in 𝓝[Ioo c 1] c, s∈Ioo c 1 := eventually_mem_nhdsWithin
  have pathEq s (hs : s∈Ioo c 1) := root_on_path (low.trans hs.1.le) hs.2 (osc s hs)
  have qlim : Tendsto id (𝓝[Ioo c 1] c) (𝓝 c) := continuousWithinAt_id.tendsto
  have zero : (0:ℝ)∈Ico 0 Real.pi := ⟨le_rfl,Real.pi_pos⟩
  have ylim := height_zero_limit (Y:=fun s ↦ (upper s).im) qlim ci zero h0 (dom.mono (by
    intro s hs
    have si := (upper_spec (low.trans hs.1.le) hs.2 (osc s hs)).2
    exact ⟨⟨ci.1.trans hs.1,hs.2⟩,⟨si.1.le,si.2⟩,(pathEq s hs).2⟩))
  have p := path_limit qlim ylim ci zero
  rw [p0] at p
  exact p.congr' (dom.mono (fun s hs ↦ (pathEq s hs).1.symm))

#print axioms upper_continuous
#print axioms upper_critical_limit
end OrderedPartitions.ThreePole
