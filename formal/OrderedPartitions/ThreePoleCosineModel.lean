import OrderedPartitions.ThreePolePhysicalResidues
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Set
open scoped ComplexConjugate

def poleMass (n : ℕ) (q : ℝ) (z : ℂ) := ‖first q z‖*‖z‖^(n+1)/2
def rowScale (n : ℕ) (q : ℝ) (z : ℂ) := poleMass n q z/((1-q)*n.factorial)
def phase (n : ℕ) (q : ℝ) (z : ℂ) := ((n+1:ℕ):ℝ)*z.arg+(first q z).arg
def realError (n : ℕ) (q : ℝ) (z : ℂ) := poleMass n q z*(contour q n).re

theorem rowScale_pos {q : ℝ} (q1 : q<1) {z : ℂ} (zn : z≠0) (ds : first q z≠0) (n : ℕ) :
    0 < rowScale n q z := by
  unfold rowScale poleMass
  exact div_pos (div_pos (mul_pos (norm_pos_iff.mpr ds) (pow_pos (norm_pos_iff.mpr zn) _)) (by norm_num))
    (mul_pos (sub_pos.mpr q1) (by positivity))

theorem realError_bound {q : ℝ} (hq : 69/100≤q) (q1 : q<1) (z : ℂ) (n : ℕ) :
    |realError n q z| ≤ 18*‖first q z‖*(‖z‖/2)^(n+1) := by
  have b := (Complex.abs_re_le_norm (contour q n)).trans (contour_bound hq q1.le n)
  unfold realError poleMass
  rw [abs_mul,abs_of_nonneg (show 0≤‖first q z‖*‖z‖^(n+1)/2 by positivity)]
  calc
    _ ≤ (‖first q z‖*‖z‖^(n+1)/2)*(36/2^(n+1)) := by gcongr
    _ = _ := by rw [div_pow];ring
private theorem inverse_product_re {w z : ℂ} (wn : w ≠ 0) (zn : z ≠ 0) (m : ℕ) :
    ((w*z^m)⁻¹).re =
      Real.cos ((m:ℝ)*z.arg+w.arg) / (‖w‖*‖z‖^m) := by
  let s := ‖w‖*‖z‖^m
  have sp : 0 < s := mul_pos (norm_pos_iff.mpr wn) (pow_pos (norm_pos_iff.mpr zn) _)
  have zp : z^m = (↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I)) := by
    rw [Complex.exp_nat_mul, ← mul_pow, Complex.norm_mul_exp_arg_mul_I]
  have polar : w*z^m = (s:ℂ)*exp (↑((m:ℝ)*z.arg+w.arg)*I) := by
    calc
      w*z^m = (↑‖w‖:ℂ) * exp (↑w.arg*I) *
          ((↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I))) := by
            rw [Complex.norm_mul_exp_arg_mul_I, zp]
      _ = _ := by
        simp only [s, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
          Complex.ofReal_natCast, add_mul, mul_assoc, Complex.exp_add]
        ring
  have re : (w*z^m).re = s * Real.cos ((m:ℝ)*z.arg+w.arg) := by
    rw [polar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_re]
    simp
  have norm_eq : ‖w*z^m‖ = s := by rw [norm_mul, norm_pow]
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq, norm_eq, re]
  field_simp [sp.ne']
  dsimp [s]
  ring

theorem cosine_model {q v : ℝ} {z : ℂ} (hq : 69/100≤q) (q1 : q<1)
    (osc : 0<axis q (branch true q)) (gz : G q z=0) (iz : z.im∈Ioo 0 Real.pi)
    (gv : G q (-(v:ℂ))=0) (vp : 0<v) (v2 : v<2) (zr : ‖z‖<2)
    (ds : first q z ≠ 0) (dv : 0<(first q (-(v:ℂ))).re) (n : ℕ) :
    rowScale n q z*(row n 3).eval (-q/(1-q)) =
      -Real.cos (phase n q z) -
        ‖first q z‖/(2*(first q (-(v:ℂ))).re)*(-(‖z‖/v))^(n+1)+realError n q z := by
  let w := first q z
  let D := (first q (-(v:ℂ))).re
  have z0 : z≠0 := fun zero ↦ iz.1.ne' (by rw [zero];rfl)
  have dreal : first q (-(v:ℂ)) = (D:ℂ) := by
    apply Complex.ext
    · rfl
    · simp [first,Complex.mul_im,Complex.exp_im]
  have res := physical_residues hq q1 osc gz iz gv vp v2 zr ds dv n
  have cj : (star w)⁻¹/(star z)^(n+1) = conj (w⁻¹/z^(n+1)) := by simp [map_div₀]
  have sr : (w⁻¹/z^(n+1)).re = Real.cos (phase n q z)/(‖w‖*‖z‖^(n+1)) := by
    rw [show w⁻¹/z^(n+1)=(w*z^(n+1))⁻¹ by simp [div_eq_mul_inv,mul_comm]]
    exact inverse_product_re ds z0 _
  have lhs : Complex.ofReal ((row n 3).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) =
      (( (row n 3).eval (-q/(1-q))/((1-q)*(n.factorial:ℝ)):ℝ):ℂ) := by push_cast;rfl
  have rt : (first q (-(v:ℂ)))⁻¹/(-(v:ℂ))^(n+1) = ((D⁻¹/(-v)^(n+1):ℝ):ℂ) := by
    rw [dreal];push_cast;rfl
  change _=contour q n-w⁻¹/z^(n+1)-(star w)⁻¹/(star z)^(n+1)-_ at res
  rw [lhs,cj,rt] at res
  have re := congrArg Complex.re res
  simp only [Complex.ofReal_re,Complex.sub_re,Complex.conj_re,sr] at re
  have wn : ‖w‖≠0 := (norm_pos_iff.mpr ds).ne'
  have rz : ‖z‖≠0 := (norm_pos_iff.mpr z0).ne'
  have dn : D≠0 := dv.ne'
  have realmode : (‖w‖*‖z‖^(n+1)/2)*(D⁻¹/(-v)^(n+1)) = ‖w‖/(2*D)*(-(‖z‖/v))^(n+1) := by
    rw [show -(‖z‖/v)=‖z‖/(-v) by ring,div_pow];ring
  unfold rowScale realError poleMass
  change (‖w‖*‖z‖^(n+1)/2)/((1-q)*(n.factorial:ℝ))*_ = _-‖w‖/(2*D)*_+ (‖w‖*‖z‖^(n+1)/2)*_
  rw [←realmode,div_mul_eq_mul_div,(show (‖w‖*‖z‖^(n+1)/2)*(row n 3).eval (-q/(1-q))/((1-q)*↑n.factorial)=
    (‖w‖*‖z‖^(n+1)/2)*((row n 3).eval (-q/(1-q))/((1-q)*↑n.factorial)) by ring),re]
  field_simp [wn,rz];ring

#print axioms cosine_model
end OrderedPartitions.ThreePole
