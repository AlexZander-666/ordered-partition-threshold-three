import OrderedPartitions.ThreePoleOriginalTaylor
import OrderedPartitions.TwoPoleFiniteBrackets

/-! Integer evaluation and root readout for the finite threshold-three certificate. -/

namespace OrderedPartitions.ThreePoleFinite

open Polynomial InterlacingStep RootTracking

abbrev Coeffs := List ℕ

noncomputable def poly : Coeffs → ℝ[X]
  | [] => 0
  | a :: as => C (a : ℝ) + X * poly as

/-- Return the cleared value and the positive denominator power simultaneously. -/
def horner (a : ℤ) (b : ℕ) : Coeffs → ℤ × ℤ
  | [] => (0, 1)
  | c :: cs =>
      let (v, w) := horner a b cs
      let bw := b * w
      (c * bw + a * v, bw)

theorem horner_power (a : ℤ) (b : ℕ) (cs : Coeffs) :
    (horner a b cs).2 = (b : ℤ)^cs.length := by
  induction cs with
  | nil => simp [horner]
  | cons c cs ih =>
    change (b : ℤ)*(horner a b cs).2 = _
    rw [ih, List.length_cons, pow_succ']
    
theorem horner_eval (a : ℤ) (b : ℕ) (hb : 0 < b) (cs : Coeffs) :
    ((horner a b cs).1 : ℝ) = (b : ℝ)^cs.length * (poly cs).eval ((a : ℝ)/b) := by
  induction cs with
  | nil => simp [horner, poly]
  | cons c cs ih =>
    change (((c : ℤ)*((b : ℤ)*(horner a b cs).2)+a*(horner a b cs).1 : ℤ) : ℝ) = _
    rw [horner_power]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow, ih, List.length_cons,
      pow_succ', poly, eval_add, eval_C, eval_mul, eval_X]
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp [hb']

abbrev Point := ℤ × ℕ
abbrev Boxes := List (Point × Point)

noncomputable def coord (x : Point) : ℝ := (x.1 : ℝ) / x.2

def box (B : Boxes) (i : ℕ) : Point × Point := B[i]?.getD ((0,1),(0,1))

def less (a b : Point) : Bool := decide (a.1 * (b.2 : ℤ) < b.1 * (a.2 : ℤ))

theorem less_sound {a b : Point} (ha : 0 < a.2) (hb : 0 < b.2) (h : less a b = true) :
    coord a < coord b := by
  apply (div_lt_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)).mpr
  have h' := of_decide_eq_true h
  exact_mod_cast h'

def signChange (cs : Coeffs) (l r : Point) : Bool :=
  let u := (horner l.1 l.2 cs).1
  let v := (horner r.1 r.2 cs).1
  (decide (0 < u) && decide (v < 0)) || (decide (u < 0) && decide (0 < v))

theorem signChange_sound {cs : Coeffs} {l r : Point} (hl : 0 < l.2) (hr : 0 < r.2)
    (h : signChange cs l r = true) : (poly cs).eval (coord l) * (poly cs).eval (coord r) < 0 := by
  simp only [signChange, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain h | h := h
  all_goals
    have hl' : (0 : ℝ) < (l.2 : ℝ)^cs.length := pow_pos (by exact_mod_cast hl) _
    have hr' : (0 : ℝ) < (r.2 : ℝ)^cs.length := pow_pos (by exact_mod_cast hr) _
  · have hlv : (0 : ℝ) < ((horner l.1 l.2 cs).1 : ℝ) := by exact_mod_cast h.1
    have hrv : (((horner r.1 r.2 cs).1 : ℤ) : ℝ) < 0 := by exact_mod_cast h.2
    rw [horner_eval _ _ hl] at hlv
    rw [horner_eval _ _ hr] at hrv
    exact mul_neg_of_pos_of_neg (pos_of_mul_pos_right hlv hl'.le)
      (neg_of_mul_neg_right hrv hr'.le)
  · have hlv : (((horner l.1 l.2 cs).1 : ℤ) : ℝ) < 0 := by exact_mod_cast h.1
    have hrv : (0 : ℝ) < ((horner r.1 r.2 cs).1 : ℝ) := by exact_mod_cast h.2
    rw [horner_eval _ _ hl] at hlv
    rw [horner_eval _ _ hr] at hrv
    exact mul_neg_of_neg_of_pos (neg_of_mul_neg_right hlv hl'.le)
      (pos_of_mul_pos_right hrv hr'.le)

def validEnd (l r : Point) : Bool :=
  decide (0 < l.2) && decide (0 < r.2) && less l r && decide (r.1 < 0)

theorem validEnd_sound {l r : Point} (h : validEnd l r = true) :
    0 < l.2 ∧ 0 < r.2 ∧ coord l < coord r ∧ coord r < 0 := by
  simp only [validEnd, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hr⟩, lr⟩, neg⟩ := h
  exact ⟨hl, hr, less_sound hl hr lr, div_neg_of_neg_of_pos
    (by exact_mod_cast neg) (by exact_mod_cast hr)⟩

def boxesOK (d : ℕ) (B : Boxes) : Bool :=
  (List.range d).all (fun i ↦ validEnd (box B i).1 (box B i).2) &&
  (List.range (d-1)).all (fun i ↦ less (box B i).2 (box B (i+1)).1)

def signsOK (cs : Coeffs) (d : ℕ) (B : Boxes) : Bool :=
  (List.range d).all fun i ↦ signChange cs (box B i).1 (box B i).2

theorem signAt_of_signsOK {cs : Coeffs} {d : ℕ} {B : Boxes} (h : signsOK cs d B = true)
    (i : Fin d) : signChange cs (box B i).1 (box B i).2 = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr i.isLt)

private theorem open_root {p : ℝ[X]} {a b : ℝ} (order : a < b)
    (sign : p.eval a * p.eval b < 0) : ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  rcases mul_neg_iff.mp sign with ⟨apos, bneg⟩ | ⟨aneg, bpos⟩
  · obtain ⟨x, ⟨l, r⟩, eq⟩ := intermediate_value_Ioo' order.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨bneg, apos⟩)
    exact ⟨x, l, r, eq⟩
  · obtain ⟨x, ⟨l, r⟩, eq⟩ := intermediate_value_Ioo order.le p.continuous.continuousOn
      (show 0 ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨aneg, bpos⟩)
    exact ⟨x, l, r, eq⟩

private theorem increasing_of_step {d : ℕ} (xs : Fin d → ℝ)
    (step : ∀ (i : ℕ) (hi : i+1<d), xs ⟨i, by omega⟩ < xs ⟨i+1, hi⟩) :
    StrictMono xs := by
  cases d with
  | zero => intro i; exact i.elim0
  | succ d =>
    refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
    exact step i (by have := i.isLt; omega)

/-- An exact bracket family for an original row, with both endpoint denominators validated. -/
def Bracketed (n : ℕ) (B : Boxes) : Prop :=
  ∃ xs : Fin (n/3) → ℝ, RootArray (row n 3) xs ∧
    ∀ i : Fin (n/3), 0 < (box B i).1.2 ∧ 0 < (box B i).2.2 ∧
      coord (box B i).1 < xs i ∧ xs i < coord (box B i).2

theorem bracketed {cs : Coeffs} {n : ℕ} {B : Boxes}
    (coeff : poly cs = row n 3) (valid : boxesOK (n/3) B = true)
    (signs : ∀ i : Fin (n/3), signChange cs (box B i).1 (box B i).2 = true) :
    Bracketed n B := by
  obtain ⟨ends, adjacent⟩ := Bool.and_eq_true_iff.mp valid
  have endpoint (i : Fin (n/3)) := validEnd_sound
    (List.all_eq_true.mp ends i (List.mem_range.mpr i.isLt))
  have point (i : Fin (n/3)) : ∃ x, coord (box B i).1 < x ∧ x < coord (box B i).2 ∧
      (row n 3).eval x = 0 := by
    rw [← coeff]
    exact open_root (endpoint i).2.2.1 (signChange_sound (endpoint i).1 (endpoint i).2.1 (signs i))
  choose xs hx using point
  have step (i : ℕ) (hi : i + 1 < n/3) : xs ⟨i, by omega⟩ < xs ⟨i+1, hi⟩ := by
    let l : Fin (n/3) := ⟨i, by omega⟩
    let r : Fin (n/3) := ⟨i+1, hi⟩
    have gap := less_sound (endpoint l).2.1 (endpoint r).1
      (List.all_eq_true.mp adjacent i (List.mem_range.mpr (by omega)))
    exact (hx l).2.1.trans (gap.trans (hx r).1)
  have ord : StrictMono xs := increasing_of_step xs step
  obtain ⟨deg, _, pos⟩ := ThreePole.original_shape n
  refine ⟨xs, ⟨ord, fun i ↦ (hx i).2.1.trans (endpoint i).2.2.2, ?_, deg,
    fun i ↦ (hx i).2.2⟩, fun i ↦ ⟨(endpoint i).1, (endpoint i).2.1, (hx i).1, (hx i).2.1⟩⟩
  exact fun z ↦ pos.ne' (by simp [z])

def stayOK (d : ℕ) (B C : Boxes) : Bool :=
  (List.range d).all (fun i ↦ less (box B i).2 (box C i).1) &&
  (List.range (d-1)).all (fun i ↦ less (box C i).2 (box B (i+1)).1)

def riseOK (d : ℕ) (B C : Boxes) : Bool :=
  (List.range d).all fun i ↦ less (box C i).2 (box B i).1 && less (box B i).2 (box C (i+1)).1

theorem stay_pair {n m : ℕ} {B C : Boxes} (hn : n/3 = m/3)
    (p : Bracketed n B) (q : Bracketed m C) (h : stayOK (n/3) B C = true) :
    OrderedPair (n/3) (row n 3) (row m 3) := by
  obtain ⟨xs, hx, xb⟩ := p
  have q' : ∃ ys : Fin (n/3) → ℝ, RootArray (row m 3) ys ∧
      ∀ i : Fin (n/3), 0 < (box C i).1.2 ∧ 0 < (box C i).2.2 ∧
        coord (box C i).1 < ys i ∧ ys i < coord (box C i).2 := by
        unfold Bracketed at q
        rw [← hn] at q
        exact q
  obtain ⟨ys, hy, yb⟩ := q'
  obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨xs, hx, Or.inl ⟨ys, hy, ?_, ?_⟩⟩
  · intro i
    have gap := less_sound (xb i).2.1 (yb i).1
      (List.all_eq_true.mp first i (List.mem_range.mpr i.isLt))
    exact (xb i).2.2.2.trans (gap.trans (yb i).2.2.1)
  · intro i j lt
    have next : i.val+1 < n/3 := by have := j.isLt; exact lt_of_le_of_lt lt this
    let k : Fin (n/3) := ⟨i.val+1, next⟩
    have gap := less_sound (yb i).2.1 (xb k).1
      (List.all_eq_true.mp second i (List.mem_range.mpr (by omega)))
    exact ((yb i).2.2.2.trans (gap.trans (xb k).2.2.1)).trans_le (hx.ordered.monotone lt)

theorem rise_pair {n m : ℕ} {B C : Boxes} (hn : n/3+1 = m/3)
    (p : Bracketed n B) (q : Bracketed m C) (h : riseOK (n/3) B C = true) :
    OrderedPair (n/3) (row n 3) (row m 3) := by
  obtain ⟨xs, hx, xb⟩ := p
  have q' : ∃ ys : Fin (n/3+1) → ℝ, RootArray (row m 3) ys ∧
      ∀ i : Fin (n/3+1), 0 < (box C i).1.2 ∧ 0 < (box C i).2.2 ∧
        coord (box C i).1 < ys i ∧ ys i < coord (box C i).2 := by
        unfold Bracketed at q
        rw [← hn] at q
        exact q
  obtain ⟨ys, hy, yb⟩ := q'
  refine ⟨xs, hx, Or.inr ⟨ys, hy, fun i ↦ ?_⟩⟩
  obtain ⟨first, second⟩ := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp h i (List.mem_range.mpr i.isLt))
  have left := less_sound (yb i.castSucc).2.1 (xb i).1 first
  have right := less_sound (xb i).2.1 (yb i.succ).1 second
  exact ⟨(yb i.castSucc).2.2.2.trans (left.trans (xb i).2.2.1),
    (xb i).2.2.2.trans (right.trans (yb i.succ).2.2.1)⟩

#print axioms bracketed
#print axioms stay_pair
#print axioms rise_pair

end OrderedPartitions.ThreePoleFinite
