import OrderedPartitions.ThreePoleCosineModel
import OrderedPartitions.ThreePoleCornerBudget
import OrderedPartitions.ThreePoleMiddleBudget
import OrderedPartitions.ThreePoleUpperBranch
import OrderedPartitions.ThreePolePhase

noncomputable section
namespace OrderedPartitions.ThreePole
open Real Set
open ThreePolePhase

private theorem middle_sign {ψ θ E F : ℝ} (shift : 0 < sin θ) (zero : cos ψ = E)
    (old_error : |E| ≤ (2/5)*sin θ) (new_error : |F| ≤ (2/5)*sin θ) :
    0 < sin ψ * (-cos (ψ+θ)+F) := by
  have small : |cos ψ| ≤ 2/5 := by
    rw [zero]
    linarith [sin_le_one θ]
  have c2 : cos ψ ^ 2 ≤ (2/5 : ℝ)^2 := by
    rw [←sq_abs]
    gcongr
  have large : 4/5 < |sin ψ| := by
    by_contra! h
    have s2 : sin ψ ^ 2 ≤ (4/5 : ℝ)^2 := by
      rw [←sq_abs]
      gcongr
    linarith [sin_sq_add_cos_sq ψ]
  have term : |cos ψ*cos θ| ≤ (2/5)*sin θ := by
    rw [abs_mul]
    calc
      _ ≤ |cos ψ| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one θ) (abs_nonneg _)
      _ ≤ _ := by simpa only [mul_one, zero] using old_error
  have err : abs (-(cos ψ * cos θ) + F) ≤ (4/5)*sin θ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith
  rw [cos_add]
  rcases le_or_gt (sin ψ) 0 with hn | hp
  · rw [abs_of_nonpos hn] at large
    apply mul_pos_of_neg_of_neg (by linarith)
    have goal := mul_lt_mul_of_pos_right (show sin ψ < -(4/5) by linarith) shift
    linarith [(abs_le.mp err).2]
  · rw [abs_of_pos hp] at large
    apply mul_pos hp
    have goal := mul_lt_mul_of_pos_right large shift
    linarith [(abs_le.mp err).1]

private theorem phase_step (q : ℝ) (z : ℂ) (n h : ℕ) :
    phase (n+h) q z = phase n q z + (h:ℝ)*z.arg := by unfold phase;push_cast;ring

private def mode (n : ℕ) (q v : ℝ) (z : ℂ) :=
  -(‖first q z‖/(2*(first q (-(v:ℂ))).re))*(-(‖z‖/v))^(n+1)

private theorem mode_abs {q v : ℝ} {z : ℂ} (vp : 0<v) (dv : 0<(first q (-(v:ℂ))).re) (n : ℕ) :
    |mode n q v z| = ‖first q z‖/(2*(first q (-(v:ℂ))).re)*(‖z‖/v)^(n+1) := by
  unfold mode;rw [abs_mul,abs_neg,abs_pow,abs_neg,abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]

private theorem readout_at {q v : ℝ} {z : ℂ} {n h : ℕ} (hq : 69/100≤q) (q1 : q<1)
    (osc : 0<axis q (branch true q)) (gz : G q z=0) (iz : z.im∈Ioo 0 Real.pi)
    (gv : G q (-(v:ℂ))=0) (rp : 0<‖z‖) (rv : ‖z‖<v) (v2 : v<2)
    (ds : first q z ≠ 0) (dv : 0<(first q (-(v:ℂ))).re)
    (budget :
      (∀ m : ℕ, m=n ∨ m=n+h →
        ‖first q z‖/(2*(first q (-(v:ℂ))).re)*(‖z‖/v)^(m+1)+
          18*‖first q z‖*(‖z‖/2)^(m+1)<(2/5)*Real.sin ((h:ℝ)*z.arg)) ∨
      (‖first q z‖/(2*(first q (-(v:ℂ))).re)*(‖z‖/v)^(n+1)+
          18*‖first q z‖*(‖z‖/2)^(n+1)<6/25 ∧
       |(-(‖z‖/v))^h-Real.cos ((h:ℝ)*z.arg)| ≤ (5/2)*Real.sin ((h:ℝ)*z.arg) ∧
        |realError (n+h) q z|+|realError n q z|≤Real.sin ((h:ℝ)*z.arg)/100 ∧
        0<Real.sin ((h:ℝ)*z.arg))) :
    0<rowScale n q z ∧
    |rowScale n q z*(row n 3).eval (-q/(1-q))+Real.cos (phase n q z)| ≤ 2/5 ∧
    ((row n 3).eval (-q/(1-q))=0 →
      0<Real.sin (phase n q z)*(row (n+h) 3).eval (-q/(1-q))) := by
  have vp := rp.trans rv
  have model (m) : rowScale m q z*(row m 3).eval (-q/(1-q)) =
      -Real.cos (phase m q z)+(mode m q v z+realError m q z) := by
    rw [cosine_model hq q1 osc gz iz gv vp v2 (rv.trans v2) ds dv m];unfold mode;ring
  have cost m : |mode m q v z+realError m q z| ≤ ‖first q z‖/(2*(first q (-(v:ℂ))).re)*(‖z‖/v)^(m+1)+
      18*‖first q z‖*(‖z‖/2)^(m+1) := by
    apply (abs_add_le _ _).trans
    rw [mode_abs vp dv]; linarith only [realError_bound hq q1 z m]
  have norm := rowScale_pos q1 (norm_pos_iff.mp rp) ds
  have old : rowScale n q z*(row n 3).eval (-q/(1-q))+Real.cos (phase n q z)= mode n q v z+realError n q z := by linarith [model n]
  refine ⟨norm n,?_,?_⟩
  · rw [old]
    rcases budget with mid|corner
    · linarith [cost n,mid n (Or.inl rfl),Real.sin_le_one ((h:ℝ)*z.arg)]
    · linarith [cost n,corner.1]
  intro zero
  have eq := model n
  rw [zero,mul_zero] at eq
  have next := model (n+h)
  rw [phase_step] at next
  suffices goal : 0<Real.sin (phase n q z)*(rowScale (n+h) q z*(row (n+h) 3).eval (-q/(1-q))) by
    rw [show Real.sin (phase n q z)*(rowScale (n+h) q z*(row (n+h) 3).eval (-q/(1-q))) =
      (Real.sin (phase n q z)*(row (n+h) 3).eval (-q/(1-q)))*rowScale (n+h) q z by ring] at goal
    exact pos_of_mul_pos_left goal (norm _).le
  rcases budget with mid|corner
  · rw [next]
    have e := (cost n).trans_lt (mid n (Or.inl rfl))
    have f := (cost _).trans_lt (mid _ (Or.inr rfl))
    exact middle_sign (by linarith [abs_nonneg (mode n q v z+realError n q z)]) (by linarith) e.le f.le
  obtain ⟨tiny,drift,err,sp⟩ := corner
  let l := ‖z‖/v
  have step : mode (n+h) q v z=(-l)^h*mode n q v z := by
    change _ = (-(‖z‖/v))^h*_
    simp only [mode,show n+h+1=n+1+h by omega,pow_add];ring
  have pow : |(-l)^h|≤1 := by
    have lp : 0<l := div_pos rp vp
    rw [abs_pow,abs_neg,abs_of_pos lp];exact pow_le_one₀ lp.le ((div_lt_one vp).mpr rv).le
  let er := realError (n+h) q z-(-l)^h*realError n q z
  have absE : |er|≤Real.sin ((h:ℝ)*z.arg)/100 := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    linarith [mul_le_mul_of_nonneg_right pow (abs_nonneg (realError n q z))]
  have csmall : |Real.cos (phase n q z)|≤6/25 := by
    rw [show Real.cos (phase n q z)=mode n q v z+realError n q z by linarith]
    exact (cost n).trans tiny.le
  apply sign_after_elimination sp csmall drift absE
  apply eliminate_real_mode (u:=mode n q v z) (oldError:=realError n q z) (newError:=realError (n+h) q z)
  · linarith
  · rw [step] at next;linarith
  · rfl

/-- Physical polynomial evaluation and sign for each visible parameter. -/
theorem actual_pointwise {n h : ℕ} (hn : 240≤n) (hl : 1≤h) (hh : h≤3) {e q : ℝ}
    (ep : 0<e) (etop : e≤61/50) (par : q=1-e^3/6) (visible : 3/2≤(n:ℝ)*e)
    (hq : 69/100≤q) (q1 : q<1) (osc : 0<axis q (branch true q)) :
    0<rowScale n q (upper q) ∧
    |rowScale n q (upper q)*(row n 3).eval (-q/(1-q))+Real.cos (phase n q (upper q))|≤2/5 ∧
    ((row n 3).eval (-q/(1-q))=0 →
      0<Real.sin (phase n q (upper q))*(row (n+h) 3).eval (-q/(1-q))) := by
  obtain ⟨gz,iz⟩ := upper_spec hq q1 osc
  rcases le_or_gt (1/32:ℝ) e with mid|ex
  · obtain ⟨z,v,g,im,gv,rp,rv,v2,dv,ds,bud⟩ := ThreePoleCert.middle_budget mid etop par hq q1 osc
    have same := upper_unique (by linarith) q1 g gz im iz
    subst z
    apply readout_at hq q1 osc gz iz gv rp rv v2 ds dv (Or.inl ?_)
    intro m hm
    exact bud m h (by rcases hm with rfl|rfl <;> omega) hl hh
  · obtain ⟨z,v,g,im,gv,rp,rv,v2,ds,dv,_,_,_,tail,bud,shift⟩ := corner_budget ep ex.le par
    have same := upper_unique (by linarith) q1 g gz im iz
    subst z
    obtain ⟨spos,drift⟩ := shift h hl hh
    apply readout_at hq q1 osc gz iz gv rp rv v2 ds dv (Or.inr ?_)
    refine ⟨bud n (by omega) visible,drift,?_,by linarith⟩
    linarith [realError_bound hq q1 (upper q) n,realError_bound hq q1 (upper q) (n+h),
      tail n (by omega),tail (n+h) (by omega)]

#print axioms actual_pointwise
end OrderedPartitions.ThreePole
