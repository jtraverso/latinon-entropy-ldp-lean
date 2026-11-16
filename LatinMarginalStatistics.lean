module

public import SymbolMixtureMoments

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_marginal_statistic {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (g : LatinCell n → Fin n → ℝ) :
    (∑ xy : LatinCell n, ∑ z : Fin n, latinFamilyMarginal S w xy z*g xy z) =
      ∑ L ∈ S, w L*∑ xy : LatinCell n, g xy (latinCellValue xy L) := by
  have hxy : ∀ xy : LatinCell n,
      (∑ z : Fin n, latinFamilyMarginal S w xy z*g xy z) =
        ∑ L ∈ S, w L*g xy (latinCellValue xy L) := by
    intro xy
    change (∑ z : Fin n, (∑ L ∈ S, if latinCellValue xy L = z then w L else 0)*g xy z) = _
    simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro L _
    calc
      _ = ∑ z : Fin n, if latinCellValue xy L = z then w L*g xy z else 0 := by
        apply sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := by simp
  simp_rw [hxy]
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  rw [mul_sum]

end LatinonEntropy

#print axioms LatinonEntropy.latin_marginal_statistic
