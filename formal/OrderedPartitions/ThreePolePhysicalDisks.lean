import OrderedPartitions.ThreePoleNegativeCheck
import OrderedPartitions.ThreePoleJetBounds
import OrderedPartitions.ThreePoleLocalize

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open QComplex ThreePole

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem positive_table : cells.all (fun c ↦ decide (0 < c.qLo ∧ c.qLo ≤ c.qHi)) = true := by
  decide +kernel

theorem physical_disk {c : Cell} (mem : c ∈ cells) {q : ℝ}
    (ql : (c.qLo:ℝ) ≤ q) (qh : q ≤ (c.qHi:ℝ)) :
    ∃ z ∈ Metric.ball (value (c.x,c.y)) (c.radius:ℝ), G q z = 0 := by
  let z : Point := (c.x,c.y)
  let s := (c.qLo+c.qHi)/2
  let v := (c.qHi-c.qLo)/2
  let d := c.radius
  let eg := expUpper (c.x+d)
  let err := s*expError
  have ht := List.all_eq_true.mp all_taylor c mem
  have hg := List.all_eq_true.mp all_pass c mem
  simp only [Cell.taylorPass,Bool.and_eq_true] at ht
  simp only [Cell.passes,Cell.geometry,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨_,_,dp,dx,_,_,sq,dc,cv,vt,_⟩ := hg.1
  have pos := of_decide_eq_true (List.all_eq_true.mp positive_table c mem)
  have sp : 0 ≤ s := by dsimp [s]; linarith [pos.1,pos.2]
  have vp : 0 ≤ v := by dsimp [v]; linarith [pos.2]
  have ds : 0 < (d:ℝ) := by exact_mod_cast dp
  have sr : 0 ≤ (s:ℝ) := by exact_mod_cast sp
  have vr : 0 ≤ (v:ℝ) := by exact_mod_cast vp
  have xsum : c.x+d < 2 := by dsimp [d]; nlinarith [sq_nonneg c.y, cv,vt]
  have argbound : |((c.x+d:ℚ):ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (by exact_mod_cast (show 0≤c.x+d by dsimp [d]; linarith))]
    exact_mod_cast xsum.le
  have nbound : ‖value z‖ ≤ 2 := by
    have a : ‖value z‖^2 = (c.x:ℝ)^2+(c.y:ℝ)^2 := by simp [value,z,Complex.sq_norm,Complex.normSq_apply]; ring
    have b : (c.x:ℝ)^2+(c.y:ℝ)^2 < ((c.cap:ℝ)-(d:ℝ))^2 := by exact_mod_cast sq
    have cs : (c.cap:ℝ) < 2 := by exact_mod_cast cv.trans vt
    have cd : (d:ℝ) < c.cap := by exact_mod_cast dc
    nlinarith [mul_nonneg (show 0 ≤ 2-((c.cap:ℝ)-d) by linarith) (show 0 ≤ 2+((c.cap:ℝ)-d) by linarith)]
  have ex : Real.exp ((value z).re+(d:ℝ)) ≤ eg := by
    simpa [z,value,eg,expUpper] using (exp_real_interval (c.x+d) argbound).2
  have ep : 0 ≤ (eg:ℝ) := (Real.exp_pos _).le.trans ex
  have dq : |q-(s:ℝ)| ≤ (v:ℝ) := by
    apply abs_le.mpr
    dsimp [v,s]; push_cast; constructor <;> linarith
  have pp : |q-(s:ℝ)| * (2+Real.exp ((value z).re+d)) ≤ (v:ℝ)*(2+eg) := by
    gcongr
  obtain ⟨h0,h1l,h1u,h2l,h2u⟩ := jet_bounds z s sp nbound
  have re : (err:ℝ) = (s:ℝ)*(expError:ℝ) := by simp [err]
  rw [←re] at h0 h1l h1u h2l h2u
  have center := ht.2
  apply localize (q0:=(s:ℝ)) ds sr
  by_cases kind : c.multiplicity=1
  · left
    have gate : (upper (j0 z s)+err+v*(2+eg))+
        (upper (j2 z s)+err+s*eg*d)*d^2/2 < (lower (j1 z s)-err)*d := by
      dsimp only [j0,j1,j2,err,v,s,eg,d,z]
      simpa only [Cell.rouche,if_pos kind,decide_eq_true_eq] using center
    have realGate := (Rat.cast_lt (K:=ℝ)).mpr gate
    push_cast at realGate
    have lin := mul_le_mul_of_nonneg_right h1l ds.le
    have quad := mul_le_mul_of_nonneg_right h2u (sq_nonneg (d:ℝ))
    have tail : (s:ℝ)*Real.exp ((value z).re+d)*(d:ℝ)^3 ≤ (s:ℝ)*eg*(d:ℝ)^3 := by gcongr
    nlinarith only [pp,h0,quad,tail,lin,realGate,mul_nonneg (mul_nonneg sr ep) (pow_nonneg ds.le 3)]
  · right
    have gate : (upper (j0 z s)+err+v*(2+eg))+
        (upper (j1 z s)+err)*d+s*eg*d^3/6 < (lower (j2 z s)-err)*d^2/2 := by
      dsimp only [j0,j1,j2,err,v,s,eg,d,z]
      simpa only [Cell.rouche,if_neg kind,decide_eq_true_eq] using center
    have realGate := (Rat.cast_lt (K:=ℝ)).mpr gate
    push_cast at realGate
    have lin := mul_le_mul_of_nonneg_right h1u ds.le
    have quad := mul_le_mul_of_nonneg_right h2l (sq_nonneg (d:ℝ))
    have tail : (s:ℝ)*Real.exp ((value z).re+d)*(d:ℝ)^3 ≤ (s:ℝ)*eg*(d:ℝ)^3 := by gcongr
    nlinarith only [pp,h0,lin,quad,tail,realGate]

#print axioms physical_disk
end OrderedPartitions.ThreePoleCert
