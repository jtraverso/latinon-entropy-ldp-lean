module

public import CorrectedRowPolicy

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem RowCorrectionParameters.lower_pos (p : RowCorrectionParameters) : 0 < p.lower :=
  lt_min (half_pos p.a_pos) (by norm_num)

theorem RowCorrectionParameters.upper_pos (p : RowCorrectionParameters) : 0 < p.upper :=
  (p.a_pos.trans_le p.a_le_c).trans_le (le_max_left _ _)

def rowEntropyLogConstant (p : RowCorrectionParameters) : ℝ :=
  |Real.log p.lower|+|Real.log p.upper|

theorem rowEntropyLogConstant_nonneg (p : RowCorrectionParameters) : 0 ≤ rowEntropyLogConstant p :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem entry_log_band_of_bounds {n : ℕ} (hn : 0 < n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (ell C : ℝ) (hell : 0 < ell)
    (hlower : ∀ i j, Q i j ≠ 0 → ell/n ≤ Q i j) (hupper : ∀ i j, Q i j ≤ C/n)
    (i j : Fin n) (hne : Q i j ≠ 0) :
    |-Real.log (Q i j)-Real.log (n : ℝ)| ≤ |Real.log ell|+|Real.log C| := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpos : 0 < Q i j := lt_of_le_of_ne (hQ i j) (Ne.symm hne)
  have hlo : ell ≤ (n : ℝ)*Q i j := by nlinarith only [(div_le_iff₀ hnR).mp (hlower i j hne)]
  have hhi : (n : ℝ)*Q i j ≤ C := by nlinarith only [(le_div_iff₀ hnR).mp (hupper i j)]
  have hl := Real.log_le_log hell hlo
  have hu := Real.log_le_log (mul_pos hnR hpos) hhi
  have habs : |Real.log ((n : ℝ)*Q i j)| ≤ |Real.log ell|+|Real.log C| := by
    apply abs_le.mpr
    constructor
    · linarith only [hl,neg_abs_le (Real.log ell),abs_nonneg (Real.log C)]
    · linarith only [hu,le_abs_self (Real.log C),abs_nonneg (Real.log ell)]
  have he : -Real.log (Q i j)-Real.log (n : ℝ) = -Real.log ((n : ℝ)*Q i j) := by
    rw [Real.log_mul hnR.ne' hne]
    ring
  rw [he,abs_neg]
  exact habs

end LatinonEntropy

#print axioms LatinonEntropy.entry_log_band_of_bounds
