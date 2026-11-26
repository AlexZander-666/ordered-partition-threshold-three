import OrderedPartitions.ThreePoleCritical
import OrderedPartitions.ThreePoleRootReadout
import OrderedPartitions.TwoPolePhaseLimits

/-! Convert the verified oscillatory parameter interval to the original negative axis. -/

noncomputable section

namespace OrderedPartitions.ThreePole

open Filter Polynomial RootTracking Set
open scoped Topology

/-- Stop before the merging poles reach the endpoint q = 1. -/
def stopParameter (n : ℕ) : ℝ := 1-(3/(2*(n:ℝ)))^3/6

theorem critical_window {a c : ℝ} (ha : a ∈ Ioo (1:ℝ) (11/10))
    (hc : c = 1-a^2/4) : (279/400:ℝ) < c ∧ c < 3/4 := by
  have left : (1:ℝ)^2 < a^2 := pow_lt_pow_left₀ ha.1 (by norm_num) (by decide)
  have right : a^2 < (11/10:ℝ)^2 := pow_lt_pow_left₀ ha.2 (by linarith [ha.1]) (by decide)
  constructor <;> linarith

private theorem stopScale_pos {n : ℕ} (hn : 240 ≤ n) :
    0 < (3/(2*(n:ℝ))) := by
  have np : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  positivity

theorem stop_window {n : ℕ} (hn : 240 ≤ n) :
    (3/4:ℝ) < stopParameter n ∧ stopParameter n < 1 := by
  have nR : (240:ℝ) ≤ n := by exact_mod_cast hn
  have ep := stopScale_pos hn
  have bound : 3/(2*(n:ℝ)) ≤ (1/160:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 2*(n:ℝ))).mpr
    linarith
  have powB := pow_le_pow_left₀ ep.le bound 3
  have powP := pow_pos ep 3
  norm_num at powB
  constructor <;> unfold stopParameter <;> linarith

/-- The whole closed interval ending at the stop has exactly the cube-root
parameter range required by the middle and corner estimates. -/
theorem interval_scale {n : ℕ} (hn : 240 ≤ n) {q : ℝ}
    (lo : (279/400:ℝ) ≤ q) (hi : q ≤ stopParameter n) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 61/50 ∧ q = 1-e^3/6 ∧ (3/2:ℝ) ≤ (n:ℝ)*e := by
  have q1 := hi.trans_lt (stop_window hn).2
  have base : 0 < 6*(1-q) := by linarith
  let e := (6*(1-q))^(1/3:ℝ)
  have ep : 0 < e := Real.rpow_pos_of_pos base _
  have cubed : e^3 = 6*(1-q) := by
    change ((6*(1-q))^(1/3:ℝ))^3 = _
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul base.le]
    norm_num
  have param : q = 1-e^3/6 := by rw [cubed]; ring
  have top : e ≤ 61/50 := by
    apply (Odd.strictMono_pow (R := ℝ) (n := 3) (by decide)).le_iff_le.mp
    rw [cubed]
    norm_num
    linarith
  have lower : 3/(2*(n:ℝ)) ≤ e := by
    apply (Odd.strictMono_pow (R := ℝ) (n := 3) (by decide)).le_iff_le.mp
    rw [cubed]
    unfold stopParameter at hi
    linarith
  have np : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have vis := (div_le_iff₀ (show 0 < 2*(n:ℝ) by positivity)).mp lower
  refine ⟨e, ep, top, param, ?_⟩
  linarith only [vis]

private theorem mark_lt_one {x : ℝ} (hx : x < 1) :
    TwoPolePhase.negativeAxis x < 1 := by
  apply (div_lt_iff₀ (by linarith : 0 < 1-x)).mpr
  linarith

private theorem mark_involutive {x : ℝ} (hx : x < 1) :
    TwoPolePhase.negativeAxis (TwoPolePhase.negativeAxis x) = x := by
  have h := mark_lt_one hx
  unfold TwoPolePhase.negativeAxis at h ⊢
  field_simp [show 1-x ≠ 0 by linarith, show 1- -x/(1-x) ≠ 0 by linarith]
  ring

private theorem mark_antitone {x y : ℝ} (le : x ≤ y) (yl : y < 1) :
    TwoPolePhase.negativeAxis y ≤ TwoPolePhase.negativeAxis x := by
  apply (div_le_div_iff₀ (by linarith : 0 < 1-y) (by linarith : 0 < 1-x)).mpr
  nlinarith only [le]

private theorem mark_strict {x y : ℝ} (lt : x < y) (yl : y < 1) :
    TwoPolePhase.negativeAxis y < TwoPolePhase.negativeAxis x := by
  exact lt_of_le_of_ne (mark_antitone lt.le yl)
    (fun h ↦ lt.ne (by simpa only [mark_involutive yl, mark_involutive (lt.trans yl)] using
      (congrArg TwoPolePhase.negativeAxis h).symm))

/-- The finite parameter interval is reversed under the fractional-linear map.
All evaluations in the resulting comparison are of the original polynomials. -/
theorem ordered_pair_on_parameter {d : ℕ} {p P : ℝ[X]} {l u : ℝ}
    {ψ : ℝ → ℝ} (hp : p.natDegree = d) (hp0 : p ≠ 0)
    (hP : P.natDegree = d ∨ P.natDegree = d+1)
    (hlc : 0 < P.leadingCoeff) (hc : 0 < P.eval 0)
    (lp : 0 < l) (lu : l < u) (u1 : u < 1) (phase_cont : ContinuousOn ψ (Icc l u))
    (front : (d:ℝ)*Real.pi+(Real.pi-Real.pi/4) < ψ u)
    (back : ψ l < Real.pi+Real.pi/4)
    (model : ∀ q ∈ Icc l u, ∃ s e : ℝ, 0 < s ∧ |e| ≤ 2/5 ∧
       s*p.eval (TwoPolePhase.negativeAxis q) = -Real.cos (ψ q)+e)
    (sign : ∀ q ∈ Icc l u, p.eval (TwoPolePhase.negativeAxis q) = 0 →
      0 < Real.sin (ψ q)*P.eval (TwoPolePhase.negativeAxis q)) :
    OrderedPair d p P := by
  let mark := TwoPolePhase.negativeAxis
  let a := mark u
  let b := mark l
  have l1 := lu.trans u1
  have ab : a < b := mark_strict lu u1
  have bn : b < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos lp) (sub_pos.mpr l1)
  have x1 (x : ℝ) (hx : x ∈ Icc a b) : x < 1 :=
    hx.2.trans_lt (bn.trans (by norm_num))
  have mem : MapsTo mark (Icc a b) (Icc l u) := by
    intro x hx
    constructor
    · have h := mark_antitone hx.2 (mark_lt_one l1)
      simpa only [b, mark, mark_involutive l1] using h
    · have h := mark_antitone hx.1 (x1 x hx)
      simpa only [a, mark, mark_involutive u1] using h
  have continuous : ContinuousOn mark (Icc a b) := by
    apply continuousOn_id.neg.div (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact (sub_pos.mpr (x1 x hx)).ne'
  choose! s e approx using model
  apply ThreePolePhase.ordered_pair_of_signs (ψ := ψ ∘ mark)
    (E := e ∘ mark) (scale := s ∘ mark)
    hp hp0 hP hlc hc ab bn (phase_cont.comp continuous mem)
  · simpa only [Function.comp_apply, a, mark, mark_involutive u1] using front
  · simpa only [Function.comp_apply, b, mark, mark_involutive l1] using back
  · intro x hx
    simpa only [Function.comp_apply, mark, mark_involutive (x1 x hx)] using
      approx (mark x) (mem hx)
  · intro x hx zero
    simpa only [Function.comp_apply, mark, mark_involutive (x1 x hx)] using
      sign (mark x) (mem hx) (by simpa only [mark, mark_involutive (x1 x hx)] using zero)

#print axioms critical_window
#print axioms stop_window
#print axioms interval_scale
#print axioms ordered_pair_on_parameter

end OrderedPartitions.ThreePole
