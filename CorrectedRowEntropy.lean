module

public import RowEntropyBounds
public import RowLogBands

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- The row entropy loss is derived from C1 and C2 for the actual corrected
matrix. No entropy, logarithmic-band or marginal-error hypothesis is supplied. -/
theorem corrected_row_entropy_lower {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) (m : ℕ) (hm : Real.exp 2*p.upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    matrixEntropy (correctedRowMatrix hn p M h)-(n : ℝ)-
      rowEntropyLogConstant p*Real.sqrt (2*(n : ℝ)*permanentCapError m n) ≤
      permanentalEntropy (correctedRowMatrix hn p M h) := by
  let Q : Matrix (Fin n) (Fin n) ℝ := correctedRowMatrix hn p M h
  have hs : RowCorrectionOutput p M h Q := correctedRowMatrix_spec hn p M h hc
  have hcap : ∀ i j, Q i j ≤ p.upper/n := correctedRowPolicy_cap hn p M h hc
  have hlower : ∀ i j, Q i j ≠ 0 → p.lower/n ≤ Q i j := by
    intro i j hne
    rcases availability_binary h i j with hz | ho
    · exact False.elim (hne (hs.2.2.2.1 i j hz))
    · exact (hs.2.2.2.2.1 i j ho).1
  exact permanental_entropy_lower hn Q hs.2.2.1 hs.1 hs.2.1 p.upper hcap m hm hsize
    (rowEntropyLogConstant p) (rowEntropyLogConstant_nonneg p)
    (entry_log_band_of_bounds hn Q hs.2.2.1 p.lower p.upper p.lower_pos hlower hcap)

end LatinonEntropy

#print axioms LatinonEntropy.corrected_row_entropy_lower
