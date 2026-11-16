module

public import LatinWeightedReveal

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def latinFamilyMarginal {n : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (xy : LatinCell n) (z : Fin n) : ℝ :=
  ∑ L ∈ S, if latinCellValue xy L = z then w L else 0

def latinMarginalEntropy {n : ℕ} (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) : ℝ :=
  -∑ xy : LatinCell n, ∑ z : Fin n, latinFamilyMarginal S w xy z*Real.log (latinFamilyMarginal S w xy z)

theorem latinFamilyMarginal_nonneg {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 ≤ w L) (xy : LatinCell n) (z : Fin n) :
    0 ≤ latinFamilyMarginal S w xy z := by
  exact sum_nonneg (fun L hL => by split_ifs; exact hw L hL; exact le_rfl)

theorem latinFamilyMarginal_total {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (xy : LatinCell n) :
    (∑ z : Fin n, latinFamilyMarginal S w xy z) = ∑ L ∈ S, w L := by
  unfold latinFamilyMarginal
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  simp

theorem latinFamilyMarginal_self_ge {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 ≤ w L)
    (xy : LatinCell n) (L : LatinArray n) (hL : L ∈ S) :
    w L ≤ latinFamilyMarginal S w xy (latinCellValue xy L) := by
  have h : (if latinCellValue xy L = latinCellValue xy L then w L else 0) ≤
      latinFamilyMarginal S w xy (latinCellValue xy L) := by
    unfold latinFamilyMarginal
    exact Finset.single_le_sum
      (f := fun K : LatinArray n => if latinCellValue xy K = latinCellValue xy L then w K else 0)
      (fun K hK => by split_ifs; exact hw K hK; exact le_rfl) hL
  simpa only [ite_true] using h

theorem latin_marginal_log_sum {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) (xy : LatinCell n) :
    (∑ z : Fin n, latinFamilyMarginal S w xy z*Real.log (latinFamilyMarginal S w xy z)) =
      ∑ L ∈ S, w L*Real.log (latinFamilyMarginal S w xy (latinCellValue xy L)) := by
  change (∑ z : Fin n, (∑ L ∈ S, if latinCellValue xy L = z then w L else 0)*
    Real.log (latinFamilyMarginal S w xy z)) = _
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  calc
    _ = ∑ z : Fin n, if latinCellValue xy L = z then
        w L*Real.log (latinFamilyMarginal S w xy z) else 0 := by
      apply sum_congr rfl
      intro z _
      split_ifs <;> simp
    _ = _ := by simp

theorem latin_reference_entropy_eq {n : ℕ} (S : Finset (LatinArray n))
    (w : LatinArray n → ℝ) :
    -(∑ L ∈ S, w L*∑ xy : LatinCell n,
      Real.log (latinFamilyMarginal S w xy (latinCellValue xy L))) = latinMarginalEntropy S w := by
  unfold latinMarginalEntropy
  simp_rw [latin_marginal_log_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  rw [mul_sum]

end LatinonEntropy

#print axioms LatinonEntropy.latinFamilyMarginal_total
#print axioms LatinonEntropy.latinFamilyMarginal_self_ge
#print axioms LatinonEntropy.latin_reference_entropy_eq
