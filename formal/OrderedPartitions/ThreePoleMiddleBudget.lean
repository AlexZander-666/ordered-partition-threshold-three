import OrderedPartitions.ThreePoleDiskDerivative
import OrderedPartitions.ThreePoleDiskAngle

noncomputable section
namespace OrderedPartitions.ThreePoleCert
open ThreePole Real Complex Metric QComplex Set

private theorem high_power {x y : ℝ} (xp : 0 ≤ x) (xy : x≤y) (yu : y≤1) {n : ℕ} (hn : 240≤n) :
    x^(n+1)≤y^241 :=
  (pow_le_pow_left₀ xp xy _).trans (pow_le_pow_of_le_one (xp.trans xy) yu (by omega))

/-- The entire rational table is consumed on the actual pair of simple poles. -/
theorem middle_budget {e q : ℝ} (el : 1/32≤e) (eh : e≤61/50) (parameter : q=1-e^3/6)
    (hq : 69/100≤q) (q1 : q<1) (osc : 0<axis q (branch true q)) :
    ∃ z : ℂ, ∃ v : ℝ, G q z=0 ∧ z.im∈Ioo 0 Real.pi ∧ G q (-(v:ℂ))=0 ∧
      0<‖z‖ ∧ ‖z‖<v ∧ v<2 ∧ 0<(first q (-(v:ℂ))).re ∧ first q z≠0 ∧
      ∀ n h : ℕ, 240≤n → 1≤h → h≤3 →
      ‖first q z‖/(2*(first q (-(v:ℂ))).re)*(‖z‖/v)^(n+1)+
        18*‖first q z‖*(‖z‖/2)^(n+1) < (2/5)*Real.sin ((h:ℝ)*z.arg) := by
  obtain ⟨c,hc,lo,hi,check⟩ := actual_box el eh
  have pol := (Odd.strictMono_pow (n:=3) (by decide)).monotone lo
  have poh := (Odd.strictMono_pow (n:=3) (by decide)).monotone hi
  have ql : (c.qLo:ℝ)≤q := by dsimp [Cell.qLo];push_cast;linarith
  have qh : q≤(c.qHi:ℝ) := by dsimp [Cell.qHi];push_cast;linarith
  obtain ⟨z,zin,gz,iy,zn,_⟩ := physical_upper hc (by linarith) q1 osc ql qh
  obtain ⟨v,vb,v2,gv,Dp,Db⟩ := negative_beyond hc hq q1 ql qh
  obtain ⟨_,_,rA,AV,_⟩ := disk_norm hc zin
  have rp : 0<‖z‖ := iy.1.trans_le (Complex.im_le_norm z)
  have Ap := rp.trans rA
  have Vp := Ap.trans AV
  have vp := Vp.trans vb
  have DV := Dp.trans_le Db
  have bound := derivative_factor hc q1 ql gz zin iy.1
  refine ⟨z,v,gz,iy,gv,rp,rA.trans (AV.trans vb),v2,DV,zn,?_⟩
  intro n h hn hl hh
  obtain ⟨Spos,hsin⟩ := disk_angle_factor hc zin iy.1 hl hh
  simp only [Cell.passes,Bool.and_eq_true,Cell.budget,decide_eq_true_eq] at check
  have Hp : 0<(c.hLower:ℝ) := by exact_mod_cast check.2.2.1
  have gp : 0<(c.derivCap:ℝ) := by exact_mod_cast check.2.2.2.1
  have bq := (Rat.cast_lt (K:=ℝ)).mpr check.2.2.2.2
  unfold Cell.remainderCap at bq
  push_cast at bq
  let M := ((c.cap:ℝ)/c.negCap)^241/(2*c.negDeriv)+18*((c.cap:ℝ)/2)^241
  change (c.derivCap:ℝ)/c.hLower*M < 2/5 at bq
  rw [div_mul_eq_mul_div,div_lt_iff₀ Hp] at bq
  have b1 : (‖z‖/v)^(n+1) ≤ ((c.cap:ℝ)/c.negCap)^241 := by
    apply high_power (by positivity) _ _ hn
    · exact div_le_div₀ (by positivity) rA.le Vp vb.le
    · exact (div_le_one Vp).mpr AV.le
  have b2 : (‖z‖/2)^(n+1) ≤ ((c.cap:ℝ)/2)^241 := by
    apply high_power (by positivity) _ _ hn
    · gcongr
    · apply (div_le_one (by norm_num)).mpr;linarith
  have mass : (‖z‖/v)^(n+1)/(2*(first q (-(v:ℂ))).re)+18*(‖z‖/2)^(n+1) ≤ M := by
    dsimp [M];gcongr
  have mp : 0≤M := by dsimp [M]; positivity
  have scale := mul_le_mul bound mass (by positivity) (mul_nonneg gp.le Spos.le)
  calc
    _ = ‖first q z‖*((‖z‖/v)^(n+1)/(2*(first q (-(v:ℂ))).re)+18*(‖z‖/2)^(n+1)) := by ring
    _ ≤ ((c.derivCap:ℝ)*Real.sin z.arg)*M := scale
    _ = ((c.derivCap:ℝ)*M)*Real.sin z.arg := by ring
    _ < ((2/5)*(c.hLower:ℝ))*Real.sin z.arg := mul_lt_mul_of_pos_right bq Spos
    _ ≤ _ := by linarith only [hsin]

#print axioms middle_budget
end OrderedPartitions.ThreePoleCert
