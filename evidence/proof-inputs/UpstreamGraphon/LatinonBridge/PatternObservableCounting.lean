module

public import LatinonPatternContinuity
public import LatinonBridge.LocalObservableEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

/-- C6 instantiated with the actual vector of pattern densities.
The finite-square statistic bridge is a separate theorem. -/
theorem finite_rate_pattern_profile_entropy_count {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (z : J → ℝ) (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonPatternProfile P) z).toReal-eta)) ≤
          ((latinonEventLatinFamily (hN.trans_le hn)
            (latinonPatternProfile P ⁻¹' Metric.ball z rho)).card : ℝ) ∧
      ((latinonEventLatinFamily (hN.trans_le hn)
        (latinonPatternProfile P ⁻¹' Metric.ball z rho)).card : ℝ) ≤
          Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
            (latinonContractedRate (latinonPatternProfile P) z).toReal+eta)) :=
  finite_rate_observable_entropy_count _ (continuous_latinonPatternProfile P) z hfinite r eta hr heta

theorem closed_pattern_profile_count_upper {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (F : Set (J → ℝ)) (hF : IsClosed F) (t : ℝ)
    (ht : ∀ z ∈ F, ENNReal.ofReal t ≤ latinonContractedRate (latinonPatternProfile P) z)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ((latinonEventLatinFamily (hN.trans_le hn) (latinonPatternProfile P ⁻¹' F)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eta)) :=
  closed_observable_latin_count_upper _ (continuous_latinonPatternProfile P) F hF t ht eta heta

theorem open_pattern_profile_count_lower {J : Type*} [Fintype J]
    {k l : J → ℕ} (P : ∀ j, LatinOrderPattern (k j) (l j))
    (G : Set (J → ℝ)) (hG : IsOpen G) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∃ z ∈ G, latinonContractedRate (latinonPatternProfile P) z ≤ ENNReal.ofReal t)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t-eta)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (latinonPatternProfile P ⁻¹' G)).card : ℝ) :=
  open_observable_latin_count_lower _ (continuous_latinonPatternProfile P) G hG t ht0 ht eta heta

end LatinonEntropy

#print axioms LatinonEntropy.finite_rate_pattern_profile_entropy_count
#print axioms LatinonEntropy.closed_pattern_profile_count_upper
#print axioms LatinonEntropy.open_pattern_profile_count_lower
