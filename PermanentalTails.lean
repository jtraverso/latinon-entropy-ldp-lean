module

public import PermanentalConcentration
public import FiniteChernoff

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

/-- Two-sided form of Lemma B for every deviation 0 <= u <= n. -/
theorem permanental_deviation_le (hn : 0 < n) (m : ℕ) (c : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (hcap : ∀ i j, Q i j ≤ c/n) (hm : Real.exp 2*c ≤ m)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) :
    (∑ sigma, if u ≤ |permutationStatistic g sigma - matrixPairing Q g|
      then permanentLaw Q sigma else 0) ≤
      2*Real.exp (permanentCapError m n-u^2/(2*(n : ℝ))) := by
  have hper := (doubly_stochastic_permanent_log_lower hn Q hQ hrow hcol).1
  exact finite_chernoff_two_sided (permanentLaw Q)
    (fun sigma => permutationStatistic g sigma - matrixPairing Q g)
    (permanentLaw_nonneg Q hQ hper) (sum_permanentLaw Q hper.ne')
    n (permanentCapError m n) u (Nat.cast_pos.mpr hn) hu0 hun
    (fun t ht => permanental_log_mgf_le hn m c Q hQ hrow hcol hcap hm g hg t ht)

end LatinonEntropy

#print axioms LatinonEntropy.permanental_deviation_le
