import OrderedPartitions.ThreePoleCritical

/-! A canonical simple upper pole and its continuous extension to criticality. -/
noncomputable section
namespace OrderedPartitions.ThreePole
open Set Filter Complex
open scoped Topology Classical

private theorem sinc_level {q y : ℝ} (hq : q∈Ioo 0 1) (hy : y∈Ico 0 Real.pi) :
    q*Real.sinc y ∈ Ioo 0 1 := by
  rcases hy.1.eq_or_lt with e|pos
  · simpa [←e] using hq
  refine ⟨mul_pos hq.1 ?_,(mul_le_mul_of_nonneg_left (Real.sinc_le_one y) hq.1.le).trans_lt (by simpa using hq.2)⟩
  rw [Real.sinc_of_ne_zero pos.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi pos hy.2) pos

theorem path_limit {ι : Type*} {l : Filter ι} {Q Y : ι → ℝ} {q y : ℝ}
    (hq : Tendsto Q l (𝓝 q)) (hy : Tendsto Y l (𝓝 y))
    (qi : q∈Ioo 0 1) (yi : y∈Ico 0 Real.pi) :
    Tendsto (fun i ↦ path true (Q i) (Y i)) l (𝓝 (path true q y)) := by
  have input := hq.mul (Real.continuous_sinc.continuousAt.tendsto.comp hy)
  have xlim : Tendsto (fun i ↦ abscissa true (Q i) (Y i)) l (𝓝 (abscissa true q y)) :=
    (branch_deriv true (sinc_level qi yi)).continuousAt.tendsto.comp input
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp xlim).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp hy).mul_const Complex.I)
  have peel (a t : ℝ) : (abscissa true a t:ℂ)+(t:ℂ)*I=path true a t :=
    Complex.re_add_im (path true a t)
  change Tendsto (fun i ↦ (abscissa true (Q i) (Y i):ℂ)+(Y i:ℂ)*I) l
    (𝓝 ((abscissa true q y:ℂ)+(y:ℂ)*I)) at h
  simpa only [peel] using h

theorem height_limit {ι : Type*} {l : Filter ι} {Q Y : ι → ℝ} {q y : ℝ}
    (hq : Tendsto Q l (𝓝 q)) (hy : Tendsto Y l (𝓝 y))
    (qi : q∈Ioo 0 1) (yi : y∈Ico 0 Real.pi) :
    Tendsto (fun i ↦ height true (Q i) (Y i)) l (𝓝 (height true q y)) := by
  have p := path_limit hq hy qi yi
  have qr := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  apply Complex.continuous_re.continuousAt.tendsto.comp
  unfold G
  exact (((tendsto_const_nhds.sub (qr.const_mul 2)).sub p).sub ((p.pow 2).div_const 2)).add
    (qr.mul (Complex.continuous_exp.continuousAt.tendsto.comp p))

private theorem height_half_pi {q : ℝ} (hq : 69/100≤q) (q1 : q<1) :
    height true q (Real.pi/2)<0 := by
  let y := Real.pi/2
  let x := abscissa true q y
  have yp : 0<y := half_pos Real.pi_pos
  have yb : y<Real.pi := by dsimp [y];linarith [Real.pi_pos]
  have inp := sinc_level (show q∈Ioo 0 1 from ⟨by linarith,q1⟩) ⟨yp.le,yb⟩
  obtain ⟨px,eq⟩ := branch_spec true inp
  change 0<x at px
  change profile x=q*Real.sinc y at eq
  have xl : 1<x := by
    by_contra! hx
    have mono := profile_right.antitoneOn px.le (show (1:ℝ)∈Ici 0 from (zero_le_one : (0:ℝ) ≤ 1)) hx
    have val : Real.sinc y = 2/Real.pi := by
      rw [Real.sinc_of_ne_zero yp.ne'];dsimp [y];rw [Real.sin_pi_div_two];ring
    have left : 2/3 < profile 1 := by
      unfold profile
      rw [Real.exp_neg]
      have p := Real.exp_pos 1
      field_simp
      nlinarith [Real.exp_one_lt_three]
    have less : 2/Real.pi < 2/3 := by
      apply div_lt_div_of_pos_left (by norm_num) (by norm_num) Real.pi_gt_three
    rw [eq,val] at mono
    linarith [mul_le_mul_of_nonneg_right q1.le (show 0≤2/Real.pi by positivity)]
  have realval : height true q y=1-2*q-x-(x^2-y^2)/2 := by
    simp [height,G,path,x,y,pow_two,Complex.exp_re,Complex.mul_re,Complex.div_ofNat_re,
      Real.cos_pi_div_two]
  change height true q y<0
  rw [realval]
  have pi2 : y<8/5 := by dsimp [y];linarith [Real.pi_lt_d2]
  nlinarith [sq_nonneg (x-1),mul_pos (sub_pos.mpr pi2) (show 0<8/5+y by linarith)]

theorem upper_exists {q : ℝ} (hq : 69/100≤q) (q1 : q<1)
    (osc : 0<axis q (branch true q)) :
    ∃ z : ℂ, G q z=0 ∧ z.im∈Ioo 0 (Real.pi/2) := by
  have qp : 0<q := by linarith
  have source : height true q 0=axis q (branch true q) := by
    have p : path true q 0=(branch true q:ℂ) := by apply Complex.ext <;> simp [path,abscissa]
    rw [height,p,axis]
  have domain : Icc 0 (Real.pi/2) ⊆ Ico 0 Real.pi := fun t ht ↦
    ⟨ht.1,by linarith [ht.2,Real.pi_pos]⟩
  have continuous : ContinuousOn (height true q) (Icc 0 (Real.pi/2)) := fun t ht ↦
    (height_limit (Q:=fun _ : ℝ ↦ q) tendsto_const_nhds continuousWithinAt_id.tendsto
      ⟨qp,q1⟩ (domain ht))
  obtain ⟨y,yi,eq⟩ := intermediate_value_Ioo' (f:=height true q) (half_pos Real.pi_pos).le continuous
    (show 0∈Ioo (height true q (Real.pi/2)) (height true q 0) from ⟨height_half_pi hq q1,source.symm ▸ osc⟩)
  refine ⟨path true q y,Complex.ext ?_ ?_,yi⟩
  · exact eq
  · exact path_im_zero true qp q1 ⟨yi.1,by linarith [yi.2,Real.pi_pos]⟩

def upper (q : ℝ) : ℂ := if h : ∃ z : ℂ, G q z=0 ∧ z.im∈Ioo 0 (Real.pi/2) then h.choose else 0

theorem upper_spec {q : ℝ} (hq : 69/100≤q) (q1 : q<1) (osc : 0<axis q (branch true q)) :
    G q (upper q)=0 ∧ (upper q).im∈Ioo 0 Real.pi := by
  have h := upper_exists hq q1 osc
  rw [upper,dif_pos h]
  exact ⟨h.choose_spec.1,h.choose_spec.2.1,by linarith [h.choose_spec.2.2,Real.pi_pos]⟩

#print axioms upper_exists
end OrderedPartitions.ThreePole
