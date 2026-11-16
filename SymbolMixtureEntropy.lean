module

public import SymbolMixtureMoments
public import LatinCappedEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem symbol_eval_probability_le_grid_cap {n q M : ℕ} (hM : 0 < M)
    (color : Fin n → Fin q)
    (hsize : ∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber color a).card : ℝ)) (a z : Fin n) :
    symbolEvalProbability color a z ≤ (1/(M : ℝ))^2 := by
  rw [symbol_eval_probability_uniform]
  split_ifs
  · have hpos : (0 : ℝ) < (M : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hM)
    simpa only [one_div_pow] using one_div_le_one_div_of_le hpos (hsize a)
  · exact sq_nonneg _

theorem symbol_mixture_marginal_le_grid_cap {n q M : ℕ} (hM : 0 < M)
    (color : Fin n → Fin q) (S : Finset (LatinArray n)) (hS : S.Nonempty)
    (hsize : ∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber color a).card : ℝ))
    (xy : LatinCell n) (z : Fin n) :
    latinFamilyMarginal (symbolMixtureFamily color S) (symbolMixtureWeight color S) xy z ≤
      (1/(M : ℝ))^2 := by
  rw [symbol_mixture_marginal_eq]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (card_pos.mpr hS) : (0 : ℝ) < S.card)).mpr
  calc
    _ ≤ ∑ _L ∈ S, (1/(M : ℝ))^2 := sum_le_sum (fun L _ =>
      symbol_eval_probability_le_grid_cap hM color hsize (latinCellValue xy L) z)
    _ = _ := by simp; ring

/-- The marginal cap is discharged by actual symbol-block permutations.
The original family need not be invariant under these permutations. -/
theorem symbol_mixture_count_entropy_upper {n q M : ℕ} (hM : 0 < M)
    (color : Fin n → Fin q) (S : Finset (LatinArray n)) (hS : S.Nonempty)
    (hsize : ∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber color a).card : ℝ)) :
    Real.log (S.card : ℝ) ≤
      latinMarginalEntropy (symbolMixtureFamily color S) (symbolMixtureWeight color S)-2*(n : ℝ)^2+
        (n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ)) :=
  (symbol_mixture_entropy_lower color S hS).trans
    (latin_capped_marginal_entropy_upper hM _ (symbolMixtureFamily_nonempty color S hS) _
      (symbolMixtureWeight_pos color S hS) (symbolMixtureWeight_total color S hS)
      (symbol_mixture_marginal_le_grid_cap hM color S hS hsize))

theorem exists_symbol_mixture_entropy_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n q : ℕ) (color : Fin n → Fin q) (S : Finset (LatinArray n)),
      S.Nonempty → (∀ a, (M : ℝ)^2 ≤ ((symbolColorFiber color a).card : ℝ)) →
        Real.log (S.card : ℝ) ≤
          latinMarginalEntropy (symbolMixtureFamily color S) (symbolMixtureWeight color S)-
            2*(n : ℝ)^2+eta*(n : ℝ)^2 := by
  obtain ⟨M,hM,hentropy⟩ := exists_uniform_latin_marginal_entropy_threshold eta heta
  refine ⟨M,hM,?_⟩
  intro n q color S hS hsize
  exact (symbol_mixture_entropy_lower color S hS).trans
    (hentropy n _ _ (symbolMixtureFamily_nonempty color S hS)
      (symbolMixtureWeight_pos color S hS) (symbolMixtureWeight_total color S hS)
      (symbol_mixture_marginal_le_grid_cap hM color S hS hsize))

end LatinonEntropy

#print axioms LatinonEntropy.symbol_mixture_marginal_le_grid_cap
#print axioms LatinonEntropy.symbol_mixture_count_entropy_upper
#print axioms LatinonEntropy.exists_symbol_mixture_entropy_threshold
