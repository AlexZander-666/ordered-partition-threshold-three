import OrderedPartitions.ThreePoleAllSizes

/-! The four-row window of original large-block polynomials and its sharpness. -/
namespace OrderedPartitions.ThreePole
open RootTracking

/-- Arbitrarily late five-row windows have an endpoint pair differing by two degrees. -/
theorem five_rows_fail (m : ℕ) :
    ¬ OrderedPair ((3*m+2)/3) (row (3*m+2) 3) (row (3*m+6) 3) := by
  rintro ⟨_,_,⟨ys,hy,_⟩|⟨ys,hy,_⟩⟩ <;>
    have bad := hy.degree <;> rw [(original_shape (3*m+6)).1] at bad <;> omega

#print axioms five_rows_fail
end OrderedPartitions.ThreePole
