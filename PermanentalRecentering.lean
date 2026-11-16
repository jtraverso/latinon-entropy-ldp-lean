module

public import PermanentalMarginals
public import PermanentalTails

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

theorem matrixPairing_sub_abs_le (P Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1) :
    |matrixPairing P g - matrixPairing Q g| ≤ ∑ i, ∑ j, |P i j-Q i j| := by
  have he : matrixPairing P g - matrixPairing Q g = ∑ i, ∑ j, (P i j-Q i j)*g i j := by
    simp only [matrixPairing,sub_mul,sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, (P i j-Q i j)*g i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(P i j-Q i j)*g i j| :=
      sum_le_sum (fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg _)).trans_eq (mul_one _)))

/-- Center the finite MGF at its actual marginal expectation. This is the
form needed for conditional iteration along the row process. -/
theorem permanental_recentered_log_mgf_le (hn : 0 < n) (m : ℕ) (c : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (hcap : ∀ i j, Q i j ≤ c/n) (hm : Real.exp 2*c ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) :
    Real.log (∑ sigma, permanentLaw Q sigma * Real.exp
      (t*(permutationStatistic g sigma-matrixPairing (permanentMarginal Q) g))) ≤
      (n : ℝ)*t^2+2*permanentCapError m n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd := permanentCapError_nonneg n m hn
  have hper := (doubly_stochastic_permanent_log_lower hn Q hQ hrow hcol).1
  let delta := matrixPairing (permanentMarginal Q) g-matrixPairing Q g
  have hdelta : |delta| ≤ Real.sqrt (2*(n : ℝ)*permanentCapError m n) :=
    (matrixPairing_sub_abs_le (permanentMarginal Q) Q g hg).trans
      (permanental_marginal_l1_le hn m c Q hQ hrow hcol hcap hm hsize)
  have hsq : delta^2 ≤ 2*(n : ℝ)*permanentCapError m n := by
    have h := (sq_le_sq₀ (abs_nonneg delta) (Real.sqrt_nonneg _)).mpr hdelta
    simpa only [sq_abs,Real.sq_sqrt (by positivity : 0 ≤ 2*(n : ℝ)*permanentCapError m n)] using h
  have hyoung : -t*delta ≤ (n : ℝ)*t^2/2+permanentCapError m n := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith [sq_nonneg ((n : ℝ)*t+delta)]
  have he : (∑ sigma, permanentLaw Q sigma * Real.exp
      (t*(permutationStatistic g sigma-matrixPairing (permanentMarginal Q) g))) =
      Real.exp (-t*delta)*centeredPermanentMGF Q g t := by
    unfold centeredPermanentMGF
    rw [mul_sum]
    apply sum_congr rfl
    intro sigma _
    have hex : t*(permutationStatistic g sigma-matrixPairing (permanentMarginal Q) g) =
        (-t*delta)+t*(permutationStatistic g sigma-matrixPairing Q g) := by dsimp [delta]; ring
    rw [hex,Real.exp_add]
    ring
  have hpos : 0 < centeredPermanentMGF Q g t :=
    finite_exponential_sum_pos (permanentLaw Q)
      (fun sigma => t*(permutationStatistic g sigma-matrixPairing Q g))
      (permanentLaw_nonneg Q hQ hper) (sum_permanentLaw Q hper.ne')
  rw [he,Real.log_mul (Real.exp_pos _).ne' hpos.ne',Real.log_exp]
  have hlog := permanental_log_mgf_le hn m c Q hQ hrow hcol hcap hm g hg t ht
  linarith

end LatinonEntropy

#print axioms LatinonEntropy.permanental_recentered_log_mgf_le
