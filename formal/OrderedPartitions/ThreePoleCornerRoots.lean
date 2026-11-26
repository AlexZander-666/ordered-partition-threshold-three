import OrderedPartitions.ThreePoleCornerDisk
import OrderedPartitions.ThreePoleRealAxis

noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Real Metric Set

def omega : ℂ := ⟨1/2,Real.sqrt 3/2⟩
theorem omega_sq : omega^2=omega-1 := by
  apply Complex.ext <;> norm_num [omega,pow_two,Complex.mul_re,Complex.mul_im] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
theorem omega_cube : omega^3 = -1 := by
  rw [pow_succ,omega_sq];ring_nf;rw [omega_sq];ring
theorem omega_norm : ‖omega‖=1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 3≠0)).mp
  rw [←norm_pow,omega_cube];norm_num

theorem s3_interval : (1732/1000:ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1733/1000 := by
  constructor <;> nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]

theorem negative_corner {e : ℝ} (ep : 0<e) (eh : e≤1/32) :
    ∃ v : ℝ, G (1-e^3/6) (-(e*v:ℝ):ℂ)=0 ∧ |v-(1+5*e/12)| < e^2 := by
  obtain ⟨y,ball,gy⟩ := corner_disk ep eh (w:=-1) (by norm_num)
  have d : ‖y-((-(1+5*e/12):ℝ):ℂ)‖ < e^2 := by
    have cc : cornerCenter e (-1) = ((-(1+5*e/12):ℝ):ℂ) := by
      unfold cornerCenter;push_cast;ring
    simpa only [dist_eq_norm,cc] using mem_ball.mp ball
  let q := 1-e^3/6
  let z := (e:ℂ)*y
  have ee : e^2≤e/32 := by nlinarith [mul_nonneg (sub_nonneg.mpr eh) ep.le]
  have q0 : 0<q := by dsimp [q];nlinarith [mul_le_mul_of_nonneg_right eh (sq_nonneg e)]
  have q1 : q<1 := by dsimp [q];nlinarith [pow_pos ep 3]
  have re := (Complex.abs_re_le_norm _).trans_lt d
  have im := (Complex.abs_im_le_norm _).trans_lt d
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at re im
  have zn : z.re<0 := by
    have yn : y.re<0 := by linarith [(abs_lt.mp re).2]
    simpa [z,Complex.mul_re] using mul_neg_of_pos_of_neg ep yn
  have pi : |z.im|<Real.pi := by
    simp [z,Complex.mul_im,abs_mul,abs_of_pos ep]
    have small : |y.im|≤1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left small ep.le,Real.pi_gt_three]
  have zreal : z.im=0 := by
    rcases lt_trichotomy z.im 0 with neg|zero|pos
    · have gs : G q (star z)=0 := by rw [G_conj];simp [z,q,gy]
      have p := (positive_branch_of_zero q0 q1 gs
        (show (star z).im∈Ioo 0 Real.pi by simp [abs_of_neg neg] at pi ⊢; exact ⟨neg,pi⟩)).1
      simp [not_lt_of_ge zn.le] at p
    · exact zero
    · have r := (positive_branch_of_zero q0 q1 (z:=z) gy ⟨pos,by simpa [abs_of_pos pos] using pi⟩).1
      linarith
  have yr : y.im=0 := by simpa [z,Complex.mul_im,ep.ne'] using zreal
  have ye : y=(y.re:ℂ) := by apply Complex.ext <;> simp [yr]
  refine ⟨-y.re,?_,?_⟩
  · convert gy using 2; push_cast; rw [←ye]; ring
  · rw [show -y.re-(1+5*e/12) = -(y.re- -(1+5*e/12)) by ring,abs_neg]
    exact re

#print axioms negative_corner
end OrderedPartitions.ThreePole
