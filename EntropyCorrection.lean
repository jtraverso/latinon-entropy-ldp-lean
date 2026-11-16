module

public import CorrectedRowEntropy
public import FluidEntropy
public import LatinStoppedProcess

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem matrix_entropy_correction_lower {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hM : ∀ i j, 0 ≤ M i j)
    (hzero : ∀ i j, Q i j = 0 → M i j = 0) (G : ℝ)
    (hband : ∀ i j, Q i j ≠ 0 → |-Real.log (Q i j)-Real.log (n : ℝ)| ≤ G) :
    matrixEntropy M-(Real.log (n : ℝ)+G+1)*(∑ i, ∑ j, |Q i j-M i j|) ≤ matrixEntropy Q := by
  let L := Real.log (n : ℝ)+G+1
  have hpoint : ∀ i j, -(M i j*Real.log (M i j))-L*|Q i j-M i j| ≤ -(Q i j*Real.log (Q i j)) := by
    intro i j
    by_cases hz : Q i j = 0
    · rw [hzero i j hz,hz]
      simp only [zero_mul,neg_zero,sub_self,abs_zero,mul_zero,le_refl]
    · have hpos : 0 < Q i j := lt_of_le_of_ne (hQ i j) (Ne.symm hz)
      have hs := log_potential_step (Q i j) (M i j) hpos (hM i j)
      have hc : |Real.log (Q i j)+1| ≤ L := by
        obtain ⟨hl,hu⟩ := abs_le.mp (hband i j hz)
        have hn := Real.log_natCast_nonneg n
        apply abs_le.mpr
        constructor <;> dsimp [L] <;> linarith only [hl,hu,hn]
      have hb : (Q i j-M i j)*(Real.log (Q i j)+1) ≤ L*|Q i j-M i j| := by
        calc
          _ ≤ |(Q i j-M i j)*(Real.log (Q i j)+1)| := le_abs_self _
          _ = |Q i j-M i j| * |Real.log (Q i j)+1| := abs_mul _ _
          _ ≤ |Q i j-M i j| * L := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
          _ = _ := mul_comm _ _
      nlinarith only [hs,hb]
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => hpoint i j))
  simpa only [L,matrixEntropy,sum_sub_distrib,← mul_sum,sum_neg_distrib] using hs

theorem corrected_matrix_entropy_lower {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) :
    matrixEntropy (M h)-3*(Real.log (n : ℝ)+rowEntropyLogConstant p+1)*matrixMarginDefect (M h) ≤
      matrixEntropy (correctedRowMatrix hn p M h) := by
  let Q : Matrix (Fin n) (Fin n) ℝ := correctedRowMatrix hn p M h
  have hs : RowCorrectionOutput p M h Q := correctedRowMatrix_spec hn p M h hc
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hM : ∀ i j, 0 ≤ M h i j := by
    intro i j
    rcases availability_binary h i j with hz | ho
    · simpa only [hc.zero i j hz] using (le_refl (0 : ℝ))
    · exact (div_pos p.a_pos hnR).le.trans (hc.entries i j ho).1
  have hzero : ∀ i j, Q i j = 0 → M h i j = 0 := by
    intro i j hq
    rcases availability_binary h i j with hz | ho
    · exact hc.zero i j hz
    · have hp := (div_pos p.lower_pos hnR).trans_le (hs.2.2.2.2.1 i j ho).1
      exact False.elim (hp.ne' hq)
  have hcap : ∀ i j, Q i j ≤ p.upper/n := correctedRowPolicy_cap hn p M h hc
  have hlower : ∀ i j, Q i j ≠ 0 → p.lower/n ≤ Q i j := by
    intro i j hne
    rcases availability_binary h i j with hz | ho
    · exact False.elim (hne (hs.2.2.2.1 i j hz))
    · exact (hs.2.2.2.2.1 i j ho).1
  have he := matrix_entropy_correction_lower Q (M h) hs.2.2.1 hM hzero (rowEntropyLogConstant p)
    (entry_log_band_of_bounds hn Q hs.2.2.1 p.lower p.upper p.lower_pos hlower hcap)
  have hL : 0 ≤ Real.log (n : ℝ)+rowEntropyLogConstant p+1 :=
    add_nonneg (add_nonneg (Real.log_natCast_nonneg n) (rowEntropyLogConstant_nonneg p)) (by norm_num)
  have hcost := mul_le_mul_of_nonneg_left hs.2.2.2.2.2 hL
  unfold matrixMarginDefect
  linarith only [he,hcost]

theorem corrected_row_entropy_target_lower {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) (m : ℕ) (hm : Real.exp 2*p.upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    matrixEntropy (M h)-(n : ℝ)-rowEntropyLogConstant p*Real.sqrt (2*(n : ℝ)*permanentCapError m n)-
      3*(Real.log (n : ℝ)+rowEntropyLogConstant p+1)*matrixMarginDefect (M h) ≤
      permanentalEntropy (correctedRowMatrix hn p M h) := by
  have hrow := corrected_row_entropy_lower hn p M h hc m hm hsize
  have hcorr := corrected_matrix_entropy_lower hn p M h hc
  linarith only [hrow,hcorr]

end LatinonEntropy

#print axioms LatinonEntropy.corrected_row_entropy_target_lower
