import OrderedPartitions.ThreePoleAnalyticDisk
import OrderedPartitions.ThreePoleNegativeCheck

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Finset

def cornerModel (e : ℝ) (y : ℂ) := 6/(e:ℂ)^3*G (1-e^3/6) ((e:ℂ)*y)
def cornerBase (e : ℝ) (y : ℂ) : ℂ := 1+y^3+(e:ℂ)*(y^4/4-y)

private def rem (n : ℕ) (s : ℂ) := Complex.exp s- ∑ i ∈ range n, s^i/(i.factorial:ℂ)

private theorem corner_identity {e : ℝ} (en : e≠0) (y : ℂ) :
    cornerModel e y-cornerBase e y=6/(e:ℂ)^3*rem 5 ((e:ℂ)*y)-rem 2 ((e:ℂ)*y) := by
  have h : (e:ℂ)≠0 := by exact_mod_cast en
  norm_num [cornerModel,cornerBase,G,rem,Finset.sum_range_succ,Nat.factorial]
  field_simp; ring

theorem corner_taylor {e : ℝ} (ep : 0<e) (y : ℂ) :
    ‖cornerModel e y-cornerBase e y‖ ≤
      e^2*Real.exp (e*‖y‖)*(‖y‖^2/2+‖y‖^5/20) := by
  have n5 := exp_remainder ((e:ℂ)*y) 5
  have n2 := exp_remainder ((e:ℂ)*y) 2
  change ‖rem 5 _‖≤_ at n5
  change ‖rem 2 _‖≤_ at n2
  rw [corner_identity ep.ne']
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
  norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep,Nat.factorial] at n5 n2 ⊢
  calc
    _ ≤ (6/e^3)*((e*‖y‖)^5/120*Real.exp (e*‖y‖)) + ((e*‖y‖)^2/2*Real.exp (e*‖y‖)) := by gcongr
    _ = _ := by field_simp;ring

private theorem exp_num : Real.exp (51/1600) < 26/25 := by
  have h := (ThreePoleCert.exp_real_interval (51/1600) (by norm_num)).2
  have rational : (ThreePoleCert.QComplex.expTaylor (51/1600,0)).1+
      ThreePoleCert.QComplex.expError < 26/25 := by decide +kernel
  have hr := (Rat.cast_lt (K:=ℝ)).mpr rational
  push_cast at h hr
  exact h.trans_lt hr

theorem corner_tail_bound {e : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ} (yn : ‖y‖ ≤ 51/50) :
    ‖cornerModel e y-cornerBase e y‖ ≤
      e^2*(26/25)*((51/50)^2/2+(51/50)^5/20) := by
  apply (corner_taylor ep y).trans
  have prod : e*‖y‖ ≤ (1/32)*(51/50) := by gcongr
  have ee : Real.exp (e*‖y‖) ≤ 26/25 := by
    apply (Real.exp_le_exp.mpr prod).trans
    convert exp_num.le using 2; norm_num
  gcongr

#print axioms corner_tail_bound
end OrderedPartitions.ThreePole
