import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Basic

namespace OrderedPartitions.ThreePole
open Finset

/-- Sharp factorial tail of the complex exponential valid on any disk. -/
theorem exp_remainder (z : ℂ) (j : ℕ) :
    ‖Complex.exp z-∑ i ∈ range j, z^i/(i.factorial:ℂ)‖ ≤
      ‖z‖^j/(j.factorial:ℝ)*Real.exp ‖z‖ := by
  set x := ‖z‖
  have hx : 0 ≤ x := norm_nonneg _
  let f := fun i : ℕ ↦ x^i/(i.factorial:ℝ)
  have hf : HasSum f (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have shifted : Summable (fun i : ℕ ↦ f (i+j)) :=
    hf.summable.comp_injective (i:=fun i : ℕ ↦ i+j) (by intro a b h; exact Nat.add_right_cancel h)
  have bound (i : ℕ) : f (i+j) ≤ (x^j/(j.factorial:ℝ))*f i := by
    have h := Nat.le_of_dvd (Nat.factorial_pos (i+j)) (Nat.factorial_mul_factorial_dvd_factorial_add i j)
    have hc : (i.factorial:ℝ)*(j.factorial:ℝ) ≤ (i+j).factorial := by exact_mod_cast h
    dsimp [f]
    rw [pow_add, div_mul_div_comm, mul_comm (x^j), mul_comm (j.factorial:ℝ)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hc
  have lim := shifted.tsum_le_tsum bound (hf.summable.mul_left _)
  rw [tsum_mul_left, hf.tsum_eq] at lim
  have split := hf.summable.sum_add_tsum_nat_add j
  rw [hf.tsum_eq] at split
  refine (Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z j).trans ?_
  change Real.exp x-∑ i ∈ range j, f i ≤ _
  linarith

#print axioms exp_remainder
end OrderedPartitions.ThreePole
