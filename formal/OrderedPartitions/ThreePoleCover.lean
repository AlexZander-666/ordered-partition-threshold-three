import OrderedPartitions.ThreePoleData.All

namespace OrderedPartitions.ThreePoleCert

def Tiles : List Cell → ℚ → ℚ → Bool
  | [], a, b => decide (a=b)
  | c::cs, a, b => decide (c.lo=a) && decide (c.lo<c.hi) && Tiles cs c.hi b

theorem exists_cell_of_tiles {cs : List Cell} {a b : ℚ} {ε : ℝ}
    (tiles : Tiles cs a b = true) (ha : (a:ℝ) ≤ ε) (hb : ε ≤ (b:ℝ))
    (positiveWidth : a < b) :
    ∃ c ∈ cs, (c.lo:ℝ) ≤ ε ∧ ε ≤ (c.hi:ℝ) := by
  induction cs generalizing a with
  | nil =>
    have h : a=b := of_decide_eq_true (by simpa only [Tiles] using tiles)
    exact (positiveWidth.ne h).elim
  | cons head tail ih =>
    simp only [Tiles, Bool.and_eq_true, decide_eq_true_eq] at tiles
    obtain ⟨⟨hstart,_⟩, htail⟩ := tiles
    by_cases upper : ε ≤ (head.hi:ℝ)
    · exact ⟨head, List.mem_cons_self, hstart ▸ ha, upper⟩
    · have lo : (head.hi:ℝ) < ε := lt_of_not_ge upper
      have width : head.hi < b := by exact_mod_cast (lt_of_lt_of_le lo hb)
      obtain ⟨cell, mem, prop⟩ := ih htail lo.le width
      exact ⟨cell, List.mem_cons_of_mem _ mem, prop⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem table_tiles : Tiles cells (1/32) (61/50) = true := by decide +kernel

theorem actual_box {ε : ℝ} (lo : 1/32 ≤ ε) (hi : ε ≤ 61/50) :
    ∃ c ∈ cells, (c.lo:ℝ) ≤ ε ∧ ε ≤ (c.hi:ℝ) ∧ c.passes = true := by
  obtain ⟨c, hc, a, b⟩ := exists_cell_of_tiles table_tiles
    (ε := ε) (by norm_num; exact lo) (by norm_num; exact hi) (by norm_num)
  exact ⟨c, hc, a, b, List.all_eq_true.mp all_pass c hc⟩

#print axioms actual_box

end OrderedPartitions.ThreePoleCert
