import OrderedPartitions.ThreePoleNormBounds
import OrderedPartitions.ThreePoleFunction

noncomputable section
namespace OrderedPartitions.ThreePoleCert.QComplex
open ThreePole

def j0 (z : Point) (s : ℚ) : Point := add (add (add (1-2*s,0) (scale z (-1)))
  (scale (mult z z) (-(1/2)))) (scale (expTaylor z) s)
def j1 (z : Point) (s : ℚ) : Point := add (add (scale (expTaylor z) s) (-1,0)) (scale z (-1))
def j2 (z : Point) (s : ℚ) : Point := add (scale (expTaylor z) s) (-1,0)

private theorem value_real (s : ℚ) : value (s,0) = (s:ℂ) := by
  apply Complex.ext <;> simp [value]

private theorem jet_error (z : Point) (s : ℚ) :
    let e := (s:ℂ)*(Complex.exp (value z)-value (expTaylor z))
    G s (value z)-value (j0 z s) = e ∧
    first s (value z)-value (j1 z s) = e ∧
    second s (value z)-value (j2 z s) = e := by
  dsimp only
  simp only [j0,j1,j2,value_add,value_scale,value_mult,value_real,G,first,second]
  push_cast
  constructor
  · ring
  constructor <;> ring

private theorem norm_around {f : ℂ} {z : Point} {t : ℝ} (h : ‖f-value z‖ ≤ t) :
    (lower z:ℝ)-t ≤ ‖f‖ ∧ ‖f‖ ≤ (upper z:ℝ)+t := by
  obtain ⟨zl,zu⟩ := norm_interval z
  have a := norm_sub_norm_le f (value z)
  have b := norm_sub_norm_le (value z) f
  rw [norm_sub_rev] at b
  constructor <;> linarith

theorem jet_bounds (z : Point) (s : ℚ) (hs : 0 ≤ s) (hz : ‖value z‖ ≤ 2) :
    let err := (s:ℝ)*(expError:ℝ)
    ‖G s (value z)‖ ≤ (upper (j0 z s):ℝ)+err ∧
    (lower (j1 z s):ℝ)-err ≤ ‖first s (value z)‖ ∧
    ‖first s (value z)‖ ≤ (upper (j1 z s):ℝ)+err ∧
    (lower (j2 z s):ℝ)-err ≤ ‖second s (value z)‖ ∧
    ‖second s (value z)‖ ≤ (upper (j2 z s):ℝ)+err := by
  have h : ‖(s:ℂ)*(Complex.exp (value z)-value (expTaylor z))‖ ≤ (s:ℝ)*(expError:ℝ) := by
    rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,abs_of_nonneg (by exact_mod_cast hs)]
    exact mul_le_mul_of_nonneg_left (expTaylor_error z hz) (by exact_mod_cast hs)
  obtain ⟨v0,v1,v2⟩ := jet_error z s
  exact ⟨(norm_around (v0.symm ▸ h)).2,(norm_around (v1.symm ▸ h)).1,
    (norm_around (v1.symm ▸ h)).2,(norm_around (v2.symm ▸ h)).1,(norm_around (v2.symm ▸ h)).2⟩

#print axioms jet_bounds
end OrderedPartitions.ThreePoleCert.QComplex
