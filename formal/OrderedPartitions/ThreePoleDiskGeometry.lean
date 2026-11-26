import OrderedPartitions.ThreePoleActualMiddle
import OrderedPartitions.ThreePoleAngularSlope

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open ThreePole QComplex Complex Real Metric

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_height : cells.all (fun c ↦ decide (c.y+c.radius ≤ 1)) = true := by
  decide +kernel

theorem disk_norm {c : Cell} (hc : c∈cells) {z : ℂ}
    (hz : z∈ball (value (c.x,c.y)) (c.radius:ℝ)) :
    0<z.re ∧ z.im≤1 ∧ ‖z‖<(c.cap:ℝ) ∧ (c.cap:ℝ)<c.negCap ∧ (c.negCap:ℝ)<2 := by
  let a := value (c.x,c.y)
  have hg := List.all_eq_true.mp all_pass c hc
  simp only [Cell.passes,Cell.geometry,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨_,_,dp,dx,_,_,bound,dc,cv,v2,_⟩ := hg.1
  have ht := of_decide_eq_true (List.all_eq_true.mp table_height c hc)
  have upper : (c.y:ℝ)+c.radius≤1 := by exact_mod_cast ht
  have r : ‖z-a‖ < (c.radius:ℝ) := by simpa [dist_eq_norm] using mem_ball.mp hz
  have ax : (c.radius:ℝ)<a.re := by change (c.radius:ℝ)<c.x;exact_mod_cast dx
  have rx := (abs_lt.mp ((Complex.abs_re_le_norm (z-a)).trans_lt r)).1
  have ry := (Complex.im_le_norm (z-a)).trans_lt r
  change z.im-(c.y:ℝ)<_ at ry
  have nr : ‖a‖<(c.cap:ℝ)-c.radius := by
    have s : ‖a‖^2=(c.x:ℝ)^2+(c.y:ℝ)^2 := by simp [a,value,Complex.sq_norm,Complex.normSq_apply];ring
    have bd : (c.x:ℝ)^2+(c.y:ℝ)^2<((c.cap:ℝ)-c.radius)^2 := by exact_mod_cast bound
    have pos : (c.radius:ℝ)<c.cap := by exact_mod_cast dc
    nlinarith [norm_nonneg a]
  have sum := norm_add_le (z-a) a
  rw [sub_add_cancel] at sum
  rw [Complex.sub_re] at rx
  exact ⟨by linarith,by linarith,by linarith,by exact_mod_cast cv,by exact_mod_cast v2⟩

private theorem signed_form_bound (x y : ℝ) :
    |Real.sqrt 3*x+y| ≤ 2*Real.sqrt (x^2+y^2) ∧
      |Real.sqrt 3*x-y| ≤ 2*Real.sqrt (x^2+y^2) := by
  have h := Real.sq_sqrt (show 0≤x^2+y^2 by positivity)
  have l := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have non := Real.sqrt_nonneg (x^2+y^2)
  have B : ∀ t : ℝ, (Real.sqrt 3*x+t)^2≤4*(x^2+y^2) → |Real.sqrt 3*x+t| ≤ 2*Real.sqrt (x^2+y^2) := by
    intro t ht
    nlinarith [sq_abs (Real.sqrt 3*x+t),abs_nonneg (Real.sqrt 3*x+t)]
  constructor
  · apply B
    nlinarith [sq_nonneg (x-Real.sqrt 3*y),congrArg (fun t : ℝ ↦ t*x^2) l,congrArg (fun t : ℝ ↦ t*y^2) l]
  · rw [sub_eq_add_neg];apply B
    nlinarith [sq_nonneg (x+Real.sqrt 3*y),congrArg (fun t : ℝ ↦ t*x^2) l,congrArg (fun t : ℝ ↦ t*y^2) l]

theorem form_bounds {c : Cell} {z : ℂ} (hc : c∈cells)
    (hz : z∈ball (value (c.x,c.y)) (c.radius:ℝ)) :
    0 < (173205/100000:ℝ)*c.x-c.y-2*c.radius ∧
    (173205/100000:ℝ)*c.x-c.y-2*c.radius ≤ Real.sqrt 3*z.re-z.im ∧
    (173205/100000:ℝ)*c.x+c.y-2*c.radius ≤ Real.sqrt 3*z.re+z.im := by
  let a := value (c.x,c.y)
  have hg := List.all_eq_true.mp all_pass c hc
  simp only [Cell.passes,Cell.geometry,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨_,_,dp,dx,_,co,_,_,_,_,_⟩ := hg.1
  have cs := (Rat.cast_lt (K:=ℝ)).mpr co
  push_cast at cs
  have xpos : 0<(c.x:ℝ) := by exact_mod_cast (dp.trans dx)
  have sr : (173205/100000:ℝ)≤Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)];norm_num
  have increase := mul_le_mul_of_nonneg_right sr xpos.le
  have r : ‖z-a‖ < (c.radius:ℝ) := by simpa [dist_eq_norm] using mem_ball.mp hz
  have eq : Real.sqrt ((z.re-c.x)^2+(z.im-c.y)^2)=‖z-a‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (z-a)),Complex.sq_norm]
    simp [Complex.normSq_apply,a,value,Complex.sub_re,Complex.sub_im,pow_two]
  have ⟨p,m⟩ := signed_form_bound (z.re-c.x) (z.im-c.y)
  rw [eq] at p m
  obtain ⟨pm,_⟩ := abs_le.mp p
  obtain ⟨mm,_⟩ := abs_le.mp m
  constructor
  · linarith
  constructor <;> linarith

#print axioms form_bounds
end OrderedPartitions.ThreePoleCert
