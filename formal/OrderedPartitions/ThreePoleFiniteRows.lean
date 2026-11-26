import OrderedPartitions.ThreePoleFiniteBrackets

/-! Shared coefficient checks against the original last-block recurrence. -/

namespace OrderedPartitions.ThreePoleFinite

open Finset Polynomial

def atCoeff (cs : Coeffs) (d : ℕ) : ℕ := cs[d]?.getD 0

theorem coeff_poly (cs : Coeffs) (d : ℕ) :
    (poly cs).coeff d = (atCoeff cs d : ℝ) := by
  induction cs generalizing d with
  | nil => simp [poly, atCoeff]
  | cons c cs ih =>
    cases d with
    | zero => simp [poly, atCoeff]
    | succ d => simp [poly, atCoeff, ih, coeff_X_mul]

abbrev Weights := List (ℕ × ℕ)

def weights (n : ℕ) : Weights :=
  (List.range n).map fun r ↦ (r+1, QuadraticExact.binomial n (r+1))

def term (cs : Coeffs) (rw : ℕ × ℕ) (d : ℕ) : ℕ :=
  rw.2 * (if 3 ≤ rw.1 then if d = 0 then 0 else atCoeff cs (d-1) else atCoeff cs d)

def nextCoeff (H : List Coeffs) (W : Weights) (d : ℕ) : ℕ :=
  (List.zipWith (fun cs rw ↦ term cs rw d) H W).sum

def rowOK (n : ℕ) (H : List Coeffs) (W : Weights) (cs : Coeffs) : Bool :=
  cs.length == n/3+1 &&
    (List.range (n/3+1)).all (fun d ↦ atCoeff cs d == nextCoeff H W d)

structure HistoryOK (n : ℕ) (H : List Coeffs) : Prop where
  length : H.length = n+1
  original : ∀ i ≤ n, poly (H[i]?.getD []) = row (n-i) 3

theorem historyInitial : HistoryOK 0 [[1]] := by
  refine ⟨rfl, fun i hi ↦ ?_⟩
  have h : i=0 := by omega
  subst i
  simp [poly, row_zero (by decide : 1 ≤ 3)]

theorem nextCoeff_count {n : ℕ} {H : List Coeffs} (hs : HistoryOK n H) (d : ℕ) :
    nextCoeff H (weights (n+1)) d = count (n+1) 3 d := by
  let Z := List.zipWith (fun cs rw ↦ term cs rw d) H (weights (n+1))
  have wl : (weights (n+1)).length = n+1 := by simp [weights]
  have zl : Z.length = n+1 := by simp [Z, List.length_zipWith, hs.length, wl]
  change Z.sum = _
  have rep : Z = List.ofFn (n := n+1) (fun i ↦ Z[i.val]?.getD 0) := by
    apply List.ext_getElem (by simp [zl])
    intro i hi hj
    rw [List.getElem_ofFn, List.getElem?_eq_getElem hi, Option.getD_some]
  calc
    Z.sum = (List.ofFn (n := n+1) (fun i ↦ Z[i.val]?.getD 0)).sum := congrArg List.sum rep
    _ = count (n+1) 3 d := ?_
  rw [List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Z[i]?.getD 0) (n+1), count_recurrence n (by decide : 1 ≤ 3) d]
  rw [show Icc 1 (n+1) = Ico 1 (n+2) by ext j; simp; omega, sum_Ico_eq_sum_range]
  rw [show n+2-1 = n+1 by omega]
  apply sum_congr rfl
  intro i hi
  have inZ : i < Z.length := by rw [zl]; exact mem_range.mp hi
  rw [List.getElem?_eq_getElem inZ, Option.getD_some]
  simp only [Z, List.getElem_zipWith, weights, List.getElem_map, List.getElem_range]
  have inH : i < H.length := by rw [hs.length, ← zl]; exact inZ
  have inN : i ≤ n := by have := mem_range.mp hi; omega
  have earlier (k : ℕ) : atCoeff H[i] k = count (n-i) 3 k := by
    have prev := congrArg (fun P : ℝ[X] ↦ P.coeff k) (hs.original i inN)
    rw [List.getElem?_eq_getElem inH, Option.getD_some, coeff_poly,
      coeff_row (by decide : 1 ≤ 3)] at prev
    exact_mod_cast prev
  rw [term, QuadraticExact.binomial_eq (by omega : i+1 ≤ n+1), Nat.add_comm 1 i]
  rw [show n+1-(i+1)=n-i by omega]
  simp only [earlier]

/-- Add a checked row to a table without recomputing any preceding row. -/
theorem historyPush {n : ℕ} {H : List Coeffs} {W : Weights} {cs : Coeffs}
    (hs : HistoryOK n H) (hw : W = weights (n+1)) (pass : rowOK (n+1) H W cs = true) :
    HistoryOK (n+1) (cs :: H) := by
  obtain ⟨sz, hpass⟩ := Bool.and_eq_true_iff.mp pass
  have len : cs.length = (n+1)/3+1 := beq_iff_eq.mp sz
  refine ⟨by simp [hs.length], fun i i_bound ↦ ?_⟩
  cases i with
  | zero =>
    simp only [Nat.sub_zero, List.getElem?_cons_zero, Option.getD_some]
    ext d
    rw [coeff_poly, coeff_row (by decide : 1 ≤ 3)]
    congr 1
    by_cases bound : d < cs.length
    · have check := beq_iff_eq.mp (List.all_eq_true.mp hpass d (List.mem_range.mpr (len ▸ bound)))
      rw [check, hw, nextCoeff_count hs]
    · rw [atCoeff, List.getElem?_eq_none (by omega), Option.getD_none]
      exact (count_above_degree (by decide : 1 ≤ 3) (by omega : n+1<d*3)).symm
  | succ i =>
    simpa only [List.getElem?_cons_succ, Nat.succ_sub_succ_eq_sub] using hs.original i (by omega)

theorem head_original {n : ℕ} {H : List Coeffs} {cs : Coeffs}
    (hs : HistoryOK n (cs :: H)) : poly cs = row n 3 := by
  simpa only [Nat.sub_zero, List.getElem?_cons_zero, Option.getD_some] using
    hs.original 0 (Nat.zero_le n)

#print axioms historyInitial
#print axioms historyPush
#print axioms head_original

end OrderedPartitions.ThreePoleFinite
