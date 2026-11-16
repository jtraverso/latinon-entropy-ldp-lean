module

public import PermanentalConcentration
public import WeightedJensen

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

theorem permanent_centered_expectation (Q : Matrix (Fin n) (Fin n) ℝ)
    (hper : Q.permanent ≠ 0) (g : Fin n → Fin n → ℝ) (t : ℝ) :
    (∑ sigma, permanentLaw Q sigma *
      (t * (permutationStatistic g sigma - matrixPairing Q g))) =
      t * (matrixPairing (permanentMarginal Q) g - matrixPairing Q g) := by
  have he : ∀ sigma, permanentLaw Q sigma *
      (t * (permutationStatistic g sigma - matrixPairing Q g)) =
      t * (permanentLaw Q sigma * permutationStatistic g sigma) -
        (t*matrixPairing Q g)*permanentLaw Q sigma := by intro sigma; ring
  simp_rw [he]
  rw [sum_sub_distrib,← mul_sum,← mul_sum,sum_permanentLaw Q hper,
    ← permanentMarginal_pairing Q g]
  unfold matrixPairing
  ring

theorem permanentCapError_nonneg (n m : ℕ) (hn : 0 < n) : 0 ≤ permanentCapError m n := by
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold permanentCapError
  positivity

/-- The marginal L1 estimate of Lemma B, with a completely explicit size
condition ensuring that the optimizing parameter lies in [-1,1]. -/
theorem permanental_marginal_l1_le (hn : 0 < n) (m : ℕ) (c : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (hcap : ∀ i j, Q i j ≤ c/n) (hm : Real.exp 2*c ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    (∑ i, ∑ j, |permanentMarginal Q i j - Q i j|) ≤
      Real.sqrt (2*(n : ℝ)*permanentCapError m n) := by
  classical
  have hper := (doubly_stochastic_permanent_log_lower hn Q hQ hrow hcol).1
  let g : Fin n → Fin n → ℝ :=
    fun i j => if 0 ≤ permanentMarginal Q i j - Q i j then 1 else -1
  have hg : ∀ i j, |g i j| ≤ 1 := by intro i j; dsimp [g]; split_ifs <;> norm_num
  have hgap : matrixPairing (permanentMarginal Q) g - matrixPairing Q g =
      ∑ i, ∑ j, |permanentMarginal Q i j - Q i j| := by
    unfold matrixPairing
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [← sub_mul]
    dsimp [g]
    split_ifs with h
    · rw [abs_of_nonneg h,mul_one]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  apply quadratic_moment_bound (Nat.cast_pos.mpr hn) (permanentCapError_nonneg n m hn)
    hsize (sum_nonneg (fun i _ => sum_nonneg (fun j _ => abs_nonneg _)))
  intro t ht0 ht1
  have hj := finite_exp_jensen (permanentLaw Q)
    (fun sigma => t*(permutationStatistic g sigma - matrixPairing Q g))
    (permanentLaw_nonneg Q hQ hper) (sum_permanentLaw Q hper.ne')
  rw [permanent_centered_expectation Q hper.ne' g t,hgap] at hj
  exact hj.trans (permanental_log_mgf_le hn m c Q hQ hrow hcol hcap hm g hg t
    (abs_le.mpr ⟨by linarith,ht1⟩))

end LatinonEntropy

#print axioms LatinonEntropy.permanental_marginal_l1_le
