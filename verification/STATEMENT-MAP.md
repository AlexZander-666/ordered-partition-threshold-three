# Original conjecture and formal statements

The ordered set-partition question asks about the polynomial that assigns one term to every list of nonempty disjoint blocks covering n labels. Each block of size at least j raises the exponent by one. The present result fixes j at three and allows any lower rank n, including zero. [Alexandersson’s original problem list](https://www.symmetricfunctions.com/realRootedOpenProblems.htm).

| Mathematical object or claim | Lean declaration | Interpretation |
| --- | --- | --- |
| Original coefficients | OrderedPartitions.Layer, count and coeff_row | A surjection from Fin n to Fin b records the block position of every label. Its fibers are the ordered nonempty blocks. The layer fixes the number of fibers of size at least j. |
| Original polynomial | OrderedPartitions.row | The coefficients above are used without normalization. |
| Complete negative simple roots | OrderedPartitions.InterlacingStep.RootArray and RootArray.exact | The array is strictly increasing, all entries are strictly negative zeros, and its length equals the polynomial degree. Exact factorization accounts for complex roots too. |
| Strict order | OrderedPartitions.RootTracking.OrderedPair | For equal degree the old root comes first at each index. For an increase of one, the two adjacent new roots bracket each old root. The definitions include empty arrays. |
| Exact finite proof | OrderedPartitions.ThreePoleFinite.original_finite | Lower ranks 0 through 239 and all three shifts. The coefficients and rational brackets are checked by Lean. |
| Pole expansion | OrderedPartitions.ThreePole.physical_residues | The actual value of the original polynomial at −q/(1−q), scaled by the factorial and 1−q, is identified with the contour integral and three explicit residues. |
| Uniform error and sign on the search interval | OrderedPartitions.ThreePole.actual_pointwise | At n≥240 the region with nε≥3/2 supplies the phase error and the shifted sign at a true root. |
| Locating all n≥240 roots | OrderedPartitions.ThreePole.original_analytic | Continuity, endpoint phase bounds and the exact degree turn the phase strips into complete real root arrays. |
| All sizes and shifts | OrderedPartitions.ThreePole.original_all | Every natural n and every natural h with 1≤h≤3 satisfy OrderedPair for the original rows at n and n+h. |
| Four-row windows | OrderedPartitions.ThreePole.original_four_rows | For every n and any two ordered indices in Fin 4, the original rows at n+i and n+k strictly interlace. |
| Sharpness | OrderedPartitions.ThreePole.five_rows_fail | The rows at 3m+2 and 3m+6 differ by two degrees for every natural m. This rules out a uniform five-row window. |

Other block thresholds and unordered set partitions have different statements. The adjacent-pair conjecture for arbitrary j remains separate.
