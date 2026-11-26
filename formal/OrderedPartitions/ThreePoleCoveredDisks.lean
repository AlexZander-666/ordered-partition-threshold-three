import OrderedPartitions.ThreePolePhysicalDisks

noncomputable section
namespace OrderedPartitions.ThreePoleCert

/-- All true denominators in the certified parameter window admit a zero
in the designated disk and have positive sign at the indicated negative endpoint. -/
theorem covered_physical_disks {e : ℝ} (lo : 1/32≤e) (hi : e≤61/50) :
    let q := 1-e^3/6
    ∃ c∈cells, (c.lo:ℝ) ≤ e ∧ e ≤ (c.hi:ℝ) ∧
      (∃ z ∈ Metric.ball (QComplex.value (c.x,c.y)) (c.radius:ℝ), ThreePole.G q z=0) ∧
      0 < (ThreePole.G q (-(c.negCap:ℂ))).re := by
  obtain ⟨c,hc,l,h,_⟩ := actual_box lo hi
  have h1 := (Odd.strictMono_pow (n:=3) (by decide)).monotone l
  have h2 := (Odd.strictMono_pow (n:=3) (by decide)).monotone h
  have h3 := (Odd.strictMono_pow (n:=3) (by decide)).monotone hi
  have ql : (c.qLo:ℝ) ≤ 1-e^3/6 := by dsimp [Cell.qLo]; push_cast; linarith
  have qh : 1-e^3/6 ≤ (c.qHi:ℝ) := by dsimp [Cell.qHi]; push_cast; linarith
  exact ⟨c,hc,l,h,physical_disk hc ql qh,negative_point hc (by norm_num at h3; linarith) ql qh⟩

#print axioms covered_physical_disks
end OrderedPartitions.ThreePoleCert
