import OrderedPartitions.ThreePoleResidues
import OrderedPartitions.ThreePoleRealAxis

/-! Exact coefficient formula at the two conjugate zeros and the negative real zero. -/
noncomputable section
namespace OrderedPartitions.ThreePole
open Complex Set

private theorem first_star (q : ℝ) (z : ℂ) : first q (star z) = star (first q z) := by
  simp [first,Complex.exp_conj]

/-- Only physical locations, radii and simplicity are inputs. Strip classification
and nonvanishing on the horizontal boundary supply the entire contour hypothesis. -/
theorem physical_residues {q v : ℝ} {z : ℂ} (hq : 69/100≤q) (q1 : q<1)
    (osc : 0<axis q (branch true q)) (gz : G q z=0) (iz : z.im∈Ioo 0 Real.pi)
    (vz : G q (-(v:ℂ))=0) (vp : 0<v) (v2 : v<2) (zr : ‖z‖<2)
    (ds : first q z ≠ 0) (dv : 0<(first q (-(v:ℂ))).re) (n : ℕ) :
    Complex.ofReal ((row n 3).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) =
      contour q n - (first q z)⁻¹/z^(n+1) - (star (first q z))⁻¹/(star z)^(n+1) -
      (first q (-(v:ℂ)))⁻¹/(-(v:ℂ))^(n+1) := by
  let U : Set ℂ := {w | |w.im|<Real.pi ∨ G q w≠0}
  have op : IsOpen U := (isOpen_lt Complex.continuous_im.abs continuous_const).union
    (isOpen_ne.preimage (differentiable_G q).continuous)
  have box : Box ⊆ U := by
    intro w hw
    rcases hw.2.lt_or_eq with lt|eq
    · exact Or.inl lt
    · apply Or.inr
      intro e
      have bound := rectangle_bound hq q1.le w (Or.inl eq)
      rw [e,norm_zero] at bound
      norm_num at bound
  have qp : 0<q := by linarith
  have real_unique (x : ℝ) (xe : G q (x:ℂ)=0) : x = -v := by
    obtain ⟨r,_,_,_,uniq⟩ := negative_axis hq q1
    have xneg : x<0 := by
      by_contra! h
      have pos := positive_axis qp q1 osc h
      simp [axis,xe] at pos
    exact (uniq x xneg xe).trans (uniq (-v) (by linarith) (by simpa using vz)).symm
  have exhaust : ∀ w∈U, G q w=0 → w=z ∨ w=star z ∨ w= -(v:ℂ) := by
    intro w wu gw
    have wi : |w.im|<Real.pi := wu.resolve_right (fun h ↦ h gw)
    rcases lt_trichotomy w.im 0 with neg|zero|pos
    · right; left
      have sw : G q (star w)=0 := by rw [G_conj,gw,star_zero]
      have iw : (star w).im∈Ioo 0 Real.pi := by
        change 0 < -w.im ∧ -w.im < Real.pi
        exact ⟨neg_pos.mpr neg, by simpa [abs_of_neg neg] using wi⟩
      simpa using congrArg star (upper_unique qp q1 sw gz iw iz)
    · right; right
      have realw : w=(w.re:ℂ) := by apply Complex.ext <;> simp [zero]
      have eq := real_unique w.re (by simpa only [←realw] using gw)
      calc w = (w.re:ℂ) := realw
           _ = -(v:ℂ) := by rw [eq,Complex.ofReal_neg]
    · exact Or.inl (upper_unique qp q1 gw gz ⟨pos,by simpa [abs_of_pos pos] using wi⟩ iz)
  have zn : z≠0 := fun h ↦ iz.1.ne' (by simp [h])
  have distinct : z≠star z := by
    intro h
    have e := congrArg Complex.im h
    change z.im = -z.im at e
    linarith [iz.1]
  have pair_real : z ≠ -(v:ℂ) := fun h ↦ iz.1.ne' (by simp [h])
  have conj_real : star z ≠ -(v:ℂ) := by
    intro h
    have eq := congrArg Complex.im h
    simp at eq
    exact iz.1.ne' eq
  have rv : ‖-(v:ℂ)‖<2 := by simpa [abs_of_pos vp] using v2
  have nzr : -(v:ℂ)≠0 := by exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr vp.ne')
  have starz : G q (star z)=0 := by rw [G_conj,gz,star_zero]
  have negsimple : first q (-(v:ℂ))≠0 := fun h ↦ dv.ne' (by simp [h])
  simpa only [(hasDerivAt_G q _).deriv,first_star] using
    (original_three_residues q1 op box zr (by simpa using zr) rv zn (by simpa using zn) nzr
      distinct pair_real conj_real gz starz vz (by rwa [(hasDerivAt_G q _).deriv])
      (by simpa only [(hasDerivAt_G q _).deriv,first_star,ne_eq,star_eq_zero] using ds)
      (by rwa [(hasDerivAt_G q _).deriv]) exhaust n)
#print axioms physical_residues
end OrderedPartitions.ThreePole
