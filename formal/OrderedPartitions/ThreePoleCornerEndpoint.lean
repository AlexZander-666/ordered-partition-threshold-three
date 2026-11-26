import OrderedPartitions.ThreePoleCornerBudget
import OrderedPartitions.ThreePoleCosineModel
import OrderedPartitions.ThreePoleUpperBranch

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Complex Set

theorem endpoint_phase {n : ℕ} (hn : 240≤n) :
    let e := 3/(2*(n:ℝ))
    let q := 1-e^3/6
    ((n/3:ℕ):ℝ)*Real.pi+(Real.pi-Real.pi/4) < phase n q (upper q) := by
  let e := 3/(2*(n:ℝ))
  let q := 1-e^3/6
  have nlarge : 240≤(n:ℝ) := by exact_mod_cast hn
  have np : 0<(n:ℝ) := by linarith
  have ep : 0<e := by dsimp [e];positivity
  have en : (n:ℝ)*e=3/2 := by dsimp [e];field_simp
  have eh : e≤1/32 := by dsimp [e];apply (div_le_iff₀ (by positivity)).mpr;linarith
  obtain ⟨z,v,gz,iz,_,_,_,_,_,_,low,ang,slope,_,_,_⟩ := corner_budget (q:=q) ep eh rfl
  have qp : 69/100≤q := by
    have pow : e^3≤(1/32:ℝ)^3 := by gcongr
    dsimp [q];linarith
  have q1 : q<1 := by dsimp [q];linarith [pow_pos ep 3]
  have zhalf : z.im < Real.pi/2 := by
    -- upper_spec chooses from the open upper half of the strip; use the
    -- argument bound and norm, or the monotone height with an existing root.
    obtain ⟨y,hy,gy⟩ := corner_disk ep eh omega_cube
    have yr := (rotated_disk_geometry ep eh hy).2.2.1
    have yp := (corner_angles ep eh hy).2.1
    have zp : 0<((e:ℂ)*y).im := by simpa [Complex.mul_im] using mul_pos ep yp
    have norm : ‖(e:ℂ)*y‖<1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
      nlinarith [mul_le_mul_of_nonneg_left yr.le ep.le]
    have same := upper_unique (by linarith : 0<q) q1 gz gy iz
      (show ((e:ℂ)*y).im∈Ioo 0 Real.pi from ⟨zp,by linarith [Complex.im_le_norm ((e:ℂ)*y),Real.pi_gt_three]⟩)
    rw [same];linarith [Complex.im_le_norm ((e:ℂ)*y),Real.pi_gt_three]
  have hex : ∃ w : ℂ, G q w=0 ∧ w.im∈Ioo 0 (Real.pi/2) := ⟨z,gz,iz.1,zhalf⟩
  have same : z=upper q := by
    rw [upper,dif_pos hex]
    exact upper_unique (by linarith) q1 gz hex.choose_spec.1 iz
      ⟨hex.choose_spec.2.1,by linarith [hex.choose_spec.2.2,Real.pi_pos]⟩
  change _ < phase n q (upper q)
  rw [←same]
  have d : ((n/3:ℕ):ℝ)*3 ≤ (n:ℝ) := by exact_mod_cast Nat.div_mul_le_self n 3
  have mul := mul_lt_mul_of_pos_left ang (show 0<(n:ℝ)+1 by positivity)
  have estimate : ((n:ℝ)+3)*Real.pi/3-phase n q z < Real.pi/4 := by
    unfold phase;push_cast
    nlinarith only [mul,(abs_lt.mp slope).1,en,eh,Real.pi_gt_three]
  nlinarith only [estimate,mul_le_mul_of_nonneg_right d Real.pi_pos.le]

#print axioms endpoint_phase
end OrderedPartitions.ThreePole
