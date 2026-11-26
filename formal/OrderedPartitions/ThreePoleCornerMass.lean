import OrderedPartitions.ThreePoleCornerGeometry

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Metric

theorem corner_ratio {e v : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) (hv : |v-(1+5*e/12)| < e^2) :
    1<v ∧ 0<‖y‖/v ∧ ‖y‖/v<1 ∧
      (54/100)*e < 1-‖y‖/v ∧ 1-‖y‖/v < (70/100)*e := by
  obtain ⟨lo,hi,yu,_,_,_⟩ := rotated_disk_geometry ep eh hy
  obtain ⟨vl,vh⟩ := abs_lt.mp hv
  have es : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
  have big : 1<v := by linarith
  have vp : 0<v := by linarith
  have npos : 0<‖y‖ := by linarith
  refine ⟨big,div_pos npos vp,(div_lt_one vp).mpr (yu.trans big),?_,?_⟩
  · rw [lt_sub_comm,div_lt_iff₀ vp]
    have upp : v≤1+(5/12+1/32)*e := by linarith
    nlinarith [mul_le_mul_of_nonneg_left upp ep.le]
  · rw [sub_lt_comm,lt_div_iff₀ vp]
    nlinarith [mul_le_mul_of_nonneg_left big.le ep.le]

theorem corner_residues_size {e v : ℝ} (ep : 0<e) (eh : e≤1/32) {y : ℂ}
    (hy : y∈ball (cornerCenter e omega) (e^2)) (hv : |v-(1+5*e/12)| < e^2)
    (g1 : G (1-e^3/6) ((e:ℂ)*y)=0) (g2 : G (1-e^3/6) (-(e*v:ℝ):ℂ)=0) :
    let q := 1-e^3/6
    let z := (e:ℂ)*y
    let V := e*v
    0 < (first q (-(V:ℝ):ℂ)).re ∧ ‖first q z‖ < e^2 ∧
      ‖first q z‖/(2*(first q (-(V:ℝ):ℂ)).re) < 522/1000 ∧
      ∀ n : ℕ, 1≤n → 18*‖first q z‖*(‖z‖/2)^(n+1) < e/1000 := by
  let q := 1-e^3/6
  let z := (e:ℂ)*y
  let V := e*v
  have yn := (rotated_disk_geometry ep eh hy).2.2.1
  have vp := (corner_ratio ep eh hy hv).1
  have low : (first q (-(V:ℝ):ℂ)).re = e^2*v^2/2-e^3/3 := by
    rw [first_at_root g2]; simp [-Complex.ofReal_pow,pow_two,Complex.mul_re,Complex.div_ofNat_re];ring
  have vv : 1≤v^2 := by nlinarith [sq_nonneg (v-1)]
  have vlow : e^2/2-e^3/3 ≤ (first q (-(V:ℝ):ℂ)).re := by
    rw [low]; nlinarith [mul_le_mul_of_nonneg_left vv (sq_nonneg e)]
  have es : e^3≤(1/32)*e^2 := by nlinarith [mul_le_mul_of_nonneg_right eh (sq_nonneg e)]
  have epos : 0<e^2 := sq_pos_of_pos ep
  have xp : 0<(first q (-(V:ℝ):ℂ)).re := by linarith
  have upper : ‖first q z‖ ≤ e^2/2+e^3/3 := by
    rw [first_at_root g1,show 2*(1-((1-e^3/6:ℝ):ℂ))=((e^3/3:ℝ):ℂ) by push_cast;ring]
    apply (norm_sub_le _ _).trans
    have reabs : ‖((e^3/3:ℝ):ℂ)‖=e^3/3 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [reabs,norm_div,norm_pow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep,Complex.norm_ofNat]
    have bs : e*‖y‖ ≤ e := by simpa using mul_le_mul_of_nonneg_left yn.le ep.le
    gcongr
  have un : ‖first q z‖ < e^2 := by linarith
  refine ⟨xp,un,(div_lt_iff₀ (by positivity)).mpr (by linarith),?_⟩
  intro n hn
  have zz : ‖z‖ = e*‖y‖ := by simp [z,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
  have ztiny : ‖z‖/2 ≤ (1/64:ℝ) := by rw [zz];nlinarith [mul_le_mul_of_nonneg_left yn.le ep.le]
  have powb : (‖z‖/2)^(n+1)≤(1/64:ℝ)^2 := by
    exact (pow_le_pow_left₀ (by positivity) ztiny _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have ep2 : e^2≤e/32 := by nlinarith [mul_le_mul_of_nonneg_right eh ep.le]
  change 18*‖first q z‖*(‖z‖/2)^(n+1)<e/1000
  calc
    _ ≤ 18*e^2*(1/64)^2 := by gcongr
    _ < _ := by linarith

#print axioms corner_residues_size
end OrderedPartitions.ThreePole
