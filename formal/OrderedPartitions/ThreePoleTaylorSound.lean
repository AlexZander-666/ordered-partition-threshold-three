import OrderedPartitions.ThreePoleTaylorCell
import Mathlib.Analysis.Complex.Exponential

noncomputable section
namespace OrderedPartitions.ThreePoleCert.QComplex
open Complex Finset
def value (z : Point) : ℂ := ⟨z.1,z.2⟩

theorem value_add (z w : Point) : value (add z w) = value z+value w := by
  apply Complex.ext <;> simp [value, add]
theorem value_mult (z w : Point) : value (mult z w) = value z*value w := by
  apply Complex.ext <;> simp [value, mult, Complex.mul_re, Complex.mul_im]
theorem value_scale (z : Point) (s : ℚ) : value (scale z s) = (s:ℂ)*value z := by
  apply Complex.ext <;> simp [value, scale, Complex.mul_re, Complex.mul_im]
theorem value_one : value (1,0) = 1 := by apply Complex.ext <;> simp [value]

private def horner (z : Point) (n : ℕ) (w : Point) : Point :=
  (List.range n).reverse.foldl (fun u (k : ℕ) ↦ add (1,0) (scale (mult z u) (1/((k:ℚ)+1)))) w

private theorem horner_spec (z : Point) (n : ℕ) (w : Point) :
    value (horner z n w) = ∑ i ∈ range n, (value z)^i/i.factorial +
      (value z)^n/n.factorial*value w := by
  induction n generalizing w with
  | zero => simp [horner]
  | succ n ih =>
    have step : horner z (n+1) w = horner z n (add (1,0) (scale (mult z w) (1/(n+1:ℚ)))) := by
      simp only [horner, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [step,ih, value_add, value_one, value_scale, value_mult, sum_range_succ, pow_succ,
      Nat.factorial_succ]
    push_cast
    have hz : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring

theorem value_expTaylor (z : Point) :
    value (expTaylor z) = ∑ i ∈ range 37, (value z)^i/i.factorial := by
  change value (horner z 36 (1,0)) = _
  rw [horner_spec,value_one,mul_one]
  exact (sum_range_succ _ 36).symm

theorem expTaylor_error (z : Point) (hz : ‖value z‖ ≤ 2) :
    ‖Complex.exp (value z)-value (expTaylor z)‖ ≤ (expError : ℝ) := by
  rw [value_expTaylor]
  have estimate := Complex.exp_bound' (x:=value z) (n:=37) (by norm_num; linarith)
  refine estimate.trans ?_
  calc
    ‖value z‖ ^ 37 / ((37:ℕ).factorial:ℝ) * 2 ≤ 2 ^ 37 / ((37:ℕ).factorial:ℝ) * 2 := by gcongr
    _ ≤ (expError : ℝ) := by norm_num [expError, Nat.factorial]

#print axioms expTaylor_error
end OrderedPartitions.ThreePoleCert.QComplex
