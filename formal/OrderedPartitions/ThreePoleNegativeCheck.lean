import OrderedPartitions.ThreePoleNormBounds
import OrderedPartitions.ThreePoleFunction
import OrderedPartitions.ThreePoleCover
import OrderedPartitions.ThreePoleTaylorData.All

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open QComplex

theorem exp_real_interval (x : ℚ) (hx : |(x:ℝ)| ≤ 2) :
    ((expTaylor (x,0)).1 : ℝ) - expError ≤ Real.exp x ∧
      Real.exp x ≤ ((expTaylor (x,0)).1 : ℝ) + expError := by
  have hv : value (x,0) = ((x:ℝ):ℂ) := by apply Complex.ext <;> simp [value]
  have hn : ‖value (x,0)‖ ≤ 2 := by simpa [hv] using hx
  have e := expTaylor_error (x,0) hn
  have re := Complex.abs_re_le_norm
    (Complex.exp (value (x,0))-value (expTaylor (x,0)))
  rw [hv, ←Complex.ofReal_exp] at re e
  have ab := abs_le.mp (re.trans e)
  simp only [Complex.sub_re, Complex.ofReal_re, value] at ab
  constructor <;> linarith

theorem negative_point {c : Cell} (hm : c ∈ cells) {q : ℝ}
    (hqp : 0 ≤ q) (hl : (c.qLo:ℝ) ≤ q) (hh : q ≤ (c.qHi:ℝ)) :
    0 < (ThreePole.G q (-(c.negCap:ℂ))).re := by
  let V := c.negCap
  let E : ℚ := (expTaylor (-V,0)).1 - expError
  have ht := List.all_eq_true.mp all_taylor c hm
  have hp := List.all_eq_true.mp all_pass c hm
  simp only [Cell.passes, Bool.and_eq_true] at hp
  have geom := hp.1
  simp only [Cell.geometry,decide_eq_true_eq] at geom
  obtain ⟨clo, chi, dr,_,_,_,_, ac, cv, vtwo,_⟩ := geom
  have vp : 0 < V := dr.trans (ac.trans cv)
  simp only [Cell.taylorPass, Bool.and_eq_true] at ht
  have signed := ht.1
  change decide (0 < 1-2*c.qLo+V-V^2/2+c.qLo*E ∧
                  0 < 1-2*c.qHi+V-V^2/2+c.qHi*E) = true at signed
  have good := of_decide_eq_true signed
  have lo : 0 < 1-2*(c.qLo:ℝ)+(V:ℝ)-(V:ℝ)^2/2+(c.qLo:ℝ)*(E:ℝ) := by exact_mod_cast good.1
  have hi : 0 < 1-2*(c.qHi:ℝ)+(V:ℝ)-(V:ℝ)^2/2+(c.qHi:ℝ)*(E:ℝ) := by exact_mod_cast good.2
  have xpos : 0 < (V:ℝ) := by exact_mod_cast vp
  have xbound : |((-V:ℚ):ℝ)| ≤ 2 := by
    rw [Rat.cast_neg,abs_neg,abs_of_pos xpos]
    exact_mod_cast vtwo.le
  have lower : (E:ℝ) ≤ Real.exp (-(V:ℝ)) := by
    simpa [E] using (exp_real_interval (-V) xbound).1
  have mid : 0 < 1-2*q+(V:ℝ)-(V:ℝ)^2/2+q*(E:ℝ) := by
    rcases le_total 2 (E:ℝ) with e | e
    · nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr e)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr e)]
  change 0 < (ThreePole.G q (-(V:ℂ))).re
  have ev : (Complex.exp (-(V:ℂ))).re = Real.exp (-(V:ℝ)) := by
    simp [Complex.exp_re]
  simp [ThreePole.G,pow_two,Complex.mul_re,ev]
  nlinarith [mul_le_mul_of_nonneg_left lower hqp]

#print axioms negative_point
end OrderedPartitions.ThreePoleCert
