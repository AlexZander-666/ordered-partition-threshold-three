import OrderedPartitions.ThreePoleFiniteRows

/-! Check a whole coefficient vector with a single walk through the earlier rows. -/

namespace OrderedPartitions.ThreePoleFinite

def addRows : Coeffs → Coeffs → Coeffs
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x+y) :: addRows xs ys

theorem at_addRows (xs ys : Coeffs) (i : ℕ) :
    atCoeff (addRows xs ys) i = atCoeff xs i + atCoeff ys i := by
  induction xs generalizing ys i with
  | nil => simp [atCoeff, addRows]
  | cons x xs ih =>
    cases ys with
    | nil => simp [atCoeff, addRows]
    | cons y ys =>
      cases i with
      | zero => simp [atCoeff, addRows]
      | succ i =>
        simpa only [atCoeff, addRows, List.getElem?_cons_succ] using ih ys i

def scaleRow (k : ℕ) (cs : Coeffs) : Coeffs := cs.map (k * ·)

theorem at_scaleRow (k : ℕ) (cs : Coeffs) (i : ℕ) :
    atCoeff (scaleRow k cs) i = k * atCoeff cs i := by
  simp only [atCoeff, scaleRow, List.getElem?_map]
  cases cs[i]? <;> simp

def weightedRow (cs : Coeffs) (rw : ℕ × ℕ) : Coeffs :=
  if 3 ≤ rw.1 then 0 :: scaleRow rw.2 cs else scaleRow rw.2 cs

theorem weightedRow_at (cs : Coeffs) (rw : ℕ × ℕ) (i : ℕ) :
    atCoeff (weightedRow cs rw) i = term cs rw i := by
  by_cases large : 3 ≤ rw.1
  · cases i with
    | zero => simp [weightedRow, term, large, atCoeff]
    | succ i =>
      simp only [weightedRow, large, if_true, term, Nat.succ_ne_zero, if_false]
      change atCoeff (scaleRow rw.2 cs) i = rw.2 * atCoeff cs i
      exact at_scaleRow _ _ _
  · simp [weightedRow, term, large, at_scaleRow]

def rowSum (rows : List Coeffs) : Coeffs := rows.foldr addRows []

theorem rowSum_at (rows : List Coeffs) (i : ℕ) :
    atCoeff (rowSum rows) i = (rows.map (fun cs ↦ atCoeff cs i)).sum := by
  induction rows with
  | nil => simp [rowSum, atCoeff]
  | cons cs rs ih =>
    simp only [rowSum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [at_addRows, ih]

def nextRow (H : List Coeffs) (W : Weights) : Coeffs :=
  rowSum (List.zipWith weightedRow H W)

theorem nextRow_at (H : List Coeffs) (W : Weights) (i : ℕ) :
    atCoeff (nextRow H W) i = nextCoeff H W i := by
  simp only [nextRow, nextCoeff, rowSum_at, List.map_zipWith, weightedRow_at]

def vectorOK (n : ℕ) (H : List Coeffs) (W : Weights) (cs : Coeffs) : Bool :=
  cs.length == n/3+1 && cs == nextRow H W

/-- The whole-vector equality implies the coefficient-by-coefficient check. -/
theorem vector_sound {n : ℕ} {H : List Coeffs} {W : Weights} {cs : Coeffs}
    (cert : vectorOK n H W cs = true) : rowOK n H W cs = true := by
  obtain ⟨len, eq⟩ := Bool.and_eq_true_iff.mp cert
  have h : cs = nextRow H W := beq_iff_eq.mp eq
  refine Bool.and_eq_true_iff.mpr ⟨len, List.all_eq_true.mpr fun d _ ↦ ?_⟩
  exact beq_iff_eq.mpr (congrArg (fun L ↦ atCoeff L d) h |>.trans (nextRow_at H W d))

#print axioms vector_sound

end OrderedPartitions.ThreePoleFinite
