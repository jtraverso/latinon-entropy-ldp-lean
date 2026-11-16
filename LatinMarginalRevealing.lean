module

public import LatinFamilyMarginals
public import LatinRemainingLog

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_marginal_revealing_bound {n : ℕ} (S : Finset (LatinArray n))
    (hS : S.Nonempty) (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 < w L)
    (key : LatinCell n → ℕ) (hkey : Function.Injective key) :
    weightedFamilyEntropy S w-latinMarginalEntropy S w ≤
      ∑ L ∈ S, w L*∑ xy : LatinCell n,
        Real.log (latinRemainingReference key (latinFamilyMarginal S w) xy L) := by
  have hr : ∀ xy z, 0 ≤ latinFamilyMarginal S w xy z := fun xy z =>
    latinFamilyMarginal_nonneg S w (fun L hL => (hw L hL).le) xy z
  have hentry : ∀ xy L, L ∈ S → 0 < latinFamilyMarginal S w xy (latinCellValue xy L) :=
    fun xy L hL => (hw L hL).trans_le
      (latinFamilyMarginal_self_ge S w (fun K hK => (hw K hK).le) xy L hL)
  have hchain := latin_weighted_revealing_bound S hS w hw key hkey
    (latinFamilyMarginal S w) hr hentry
  have href := latin_reference_entropy_eq S w
  have hsplit : (∑ L ∈ S, w L*∑ xy : LatinCell n,
      (Real.log (latinRemainingReference key (latinFamilyMarginal S w) xy L)-
        Real.log (latinFamilyMarginal S w xy (latinCellValue xy L)))) =
      (∑ L ∈ S, w L*∑ xy : LatinCell n,
        Real.log (latinRemainingReference key (latinFamilyMarginal S w) xy L))+
          latinMarginalEntropy S w := by
    simp only [sum_sub_distrib,mul_sub]
    linarith only [href]
  rw [hsplit] at hchain
  linarith only [hchain]

end LatinonEntropy

#print axioms LatinonEntropy.latin_marginal_revealing_bound
