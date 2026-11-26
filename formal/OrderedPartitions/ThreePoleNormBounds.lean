import OrderedPartitions.ThreePoleTaylorSound

noncomputable section
namespace OrderedPartitions.ThreePoleCert.QComplex

/-- The integer square-root enclosure used by every Taylor disk bounds the
actual complex norm. The floor and square root are both exact. -/
theorem norm_interval (z : Point) :
    ((lower z : ℚ) : ℝ) ≤ ‖value z‖ ∧ ‖value z‖ ≤ ((upper z : ℚ) : ℝ) := by
  let u : ℚ := (z.1^2+z.2^2)*(scale23:ℚ)^2
  let N : ℕ := ⌊u⌋.toNat
  let m : ℕ := N.sqrt
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have fn : (N:ℚ) = (⌊u⌋:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hu)
  have lo : (m:ℚ)^2 ≤ u := calc
    _ ≤ (N:ℚ) := by exact_mod_cast Nat.sqrt_le' N
    _ ≤ u := fn ▸ Int.floor_le u
  have hi : u < ((m:ℚ)+1)^2 := calc
    _ < (N:ℚ)+1 := fn ▸ Int.lt_floor_add_one u
    _ ≤ _ := by exact_mod_cast Nat.lt_succ_sqrt' N
  have normSq : ‖value z‖^2 = ((z.1:ℝ)^2 + (z.2:ℝ)^2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [value, pow_two]
  have ueq : (u:ℝ)=(‖value z‖*(scale23:ℝ))^2 := by
    dsimp [u]
    push_cast
    rw [mul_pow,normSq]
  have lo' : (m:ℝ)^2 ≤ (u:ℝ) := by exact_mod_cast lo
  have hi' : (u:ℝ) < ((m:ℝ)+1)^2 := by exact_mod_cast hi
  rw [ueq] at lo' hi'
  have hs : (0:ℝ)<scale23 := by norm_num [scale23]
  have npos := norm_nonneg (value z)
  have ppos := mul_nonneg npos hs.le
  have ml : (m:ℝ) ≤ ‖value z‖*(scale23:ℝ) := by nlinarith
  have mh : ‖value z‖*(scale23:ℝ) ≤ (m:ℝ)+1 := by nlinarith
  change (( (m:ℚ)/(scale23:ℚ) : ℚ):ℝ) ≤ _ ∧ _ ≤ (((m:ℚ)/(scale23:ℚ)+1/(scale23:ℚ):ℚ):ℝ)
  push_cast
  constructor
  · exact (div_le_iff₀ hs).mpr ml
  · rw [←add_div]
    exact (le_div_iff₀ hs).mpr mh

#print axioms norm_interval
end OrderedPartitions.ThreePoleCert.QComplex
