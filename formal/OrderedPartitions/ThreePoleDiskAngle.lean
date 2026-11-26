import OrderedPartitions.ThreePoleDiskGeometry

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open ThreePole QComplex Complex Real Metric

theorem disk_angle_factor {c : Cell} (hc : c∈cells) {z : ℂ}
    (hz : z∈ball (value (c.x,c.y)) (c.radius:ℝ)) (yi : 0<z.im) {h : ℕ}
    (hl : 1≤h) (hh : h≤3) :
    0 < Real.sin z.arg ∧ (c.hLower:ℝ)*Real.sin z.arg ≤ Real.sin ((h:ℝ)*z.arg) := by
  obtain ⟨xp,_,rad,_,_⟩ := disk_norm hc hz
  obtain ⟨lpos,l,u⟩ := form_bounds hc hz
  have hg := List.all_eq_true.mp all_pass c hc
  simp only [Cell.passes,Cell.geometry,Bool.and_eq_true,decide_eq_true_eq] at hg
  have yp : 0 ≤ (c.y:ℝ) := by exact_mod_cast hg.1.2.2.2.2.1
  let L := (173205/100000:ℝ)*c.x-c.y-2*c.radius
  let U := (173205/100000:ℝ)*c.x+c.y-2*c.radius
  change 0 < L at lpos
  change L≤_ at l
  change U≤_ at u
  have up : 0<U := by dsimp [U,L] at *;linarith
  have b := mul_le_mul l u up.le (lpos.le.trans l)
  have sq := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have core : L*U≤3*z.re^2-z.im^2 := by
    nlinarith only [b,congrArg (fun t:ℝ ↦ t*z.re^2) sq]
  have sp : 0 < ‖z‖ := lt_of_lt_of_le yi (Complex.im_le_norm z)
  have cap : 0 < (c.cap:ℝ) := sp.trans rad
  have nz := norm_pos_iff.mp sp
  have nr : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  let a := Real.cos z.arg
  have co : a*‖z‖=z.re := by dsimp [a];rw [mul_comm,Complex.norm_mul_cos_arg]
  have ap : 0<a := pos_of_mul_pos_left (co ▸ xp) sp.le
  have s : 0<Real.sin z.arg := by rw [Complex.sin_arg];exact div_pos yi sp
  have hf : (c.hLower:ℝ)=min 1 (L*U/(c.cap:ℝ)^2) := by dsimp [Cell.hLower,L,U];push_cast;rfl
  have h1 : (c.hLower:ℝ)≤1 := hf ▸ min_le_left _ _
  have hr : (c.hLower:ℝ)≤4*a^2-1 := by
    rw [hf]
    apply (min_le_right _ _).trans
    have hcss : ‖z‖^2 ≤ (c.cap:ℝ)^2 := by gcongr
    have dsq := congrArg (fun u:ℝ ↦ u^2) co
    have num : (4*a^2-1)*‖z‖^2=3*z.re^2-z.im^2 := by nlinarith only [dsq,nr]
    have cp : 0<4*a^2-1 := pos_of_mul_pos_left (num ▸ (mul_pos lpos up).trans_le core) (sq_nonneg _)
    apply (div_le_iff₀ (pow_pos cap 2)).mpr
    exact (core.trans_eq num.symm).trans (mul_le_mul_of_nonneg_left hcss cp.le)
  have dpos : 0 < 4*a^2-1 := by
    have : 0 < (c.hLower:ℝ) := by rw [hf];exact lt_min (by norm_num) (div_pos (mul_pos lpos up) (pow_pos cap 2))
    exact this.trans_le hr
  have one : 1≤2*a := by nlinarith
  refine ⟨s,?_⟩
  interval_cases h
  · simpa using mul_le_mul_of_nonneg_right h1 s.le
  · norm_num [Real.sin_two_mul];dsimp [a] at one; nlinarith only [mul_le_mul_of_nonneg_right (h1.trans one) s.le]
  · have id : Real.sin (3*z.arg)=(4*a^2-1)*Real.sin z.arg := by
      rw [show 3*z.arg=2*z.arg+z.arg by ring,Real.sin_add,Real.sin_two_mul,Real.cos_two_mul];dsimp [a];ring
    norm_num; rw [id];exact mul_le_mul_of_nonneg_right hr s.le

#print axioms disk_angle_factor
end OrderedPartitions.ThreePoleCert
