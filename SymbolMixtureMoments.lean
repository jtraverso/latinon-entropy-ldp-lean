module

public import SymbolMixtureFamily
public import LatinFamilyMarginals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem symbol_mixture_moment {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (F : LatinArray n → ℝ) :
    (∑ L ∈ symbolMixtureFamily color S, symbolMixtureWeight color S L*F L) =
      finiteMean (fun g : symbolBlockStabilizer color =>
        (∑ L ∈ S, F (symbolRelabelEquiv g.val L))/(S.card : ℝ)) := by
  unfold symbolMixtureFamily symbolMixtureWeight
  rw [uniform_image_moment,symbolMixtureInput_card,Nat.cast_mul]
  simp only [symbolMixtureInput,sum_product,symbolMixtureMap]
  unfold finiteMean
  rw [← sum_div,div_div,
    mul_comm (Fintype.card (symbolBlockStabilizer color) : ℝ) (S.card : ℝ)]

theorem symbol_mixture_marginal_eq {n q : ℕ} (color : Fin n → Fin q)
    (S : Finset (LatinArray n)) (xy : LatinCell n) (z : Fin n) :
    latinFamilyMarginal (symbolMixtureFamily color S) (symbolMixtureWeight color S) xy z =
      (∑ L ∈ S, symbolEvalProbability color (latinCellValue xy L) z)/(S.card : ℝ) := by
  have h := symbol_mixture_moment color S
    (fun L => if latinCellValue xy L = z then (1 : ℝ) else 0)
  have hleft : (∑ L ∈ symbolMixtureFamily color S, symbolMixtureWeight color S L*
      (if latinCellValue xy L = z then (1 : ℝ) else 0)) =
      latinFamilyMarginal (symbolMixtureFamily color S) (symbolMixtureWeight color S) xy z := by
    unfold latinFamilyMarginal
    apply sum_congr rfl
    intro L _
    split_ifs <;> simp
  rw [hleft] at h
  have hfun : (fun g : symbolBlockStabilizer color =>
      (∑ L ∈ S, if latinCellValue xy (symbolRelabelEquiv g.val L) = z then (1 : ℝ) else 0)/(S.card : ℝ)) =
      (fun g => (1/(S.card : ℝ))*∑ L ∈ S,
        if g.val (latinCellValue xy L) = z then (1 : ℝ) else 0) := by
    funext g
    change (∑ L ∈ S, if g.val (latinCellValue xy L) = z then (1 : ℝ) else 0)/(S.card : ℝ) = _
    ring
  rw [hfun,finiteMean_mul,finiteMean_sum] at h
  change latinFamilyMarginal (symbolMixtureFamily color S) (symbolMixtureWeight color S) xy z =
    (1/(S.card : ℝ))*∑ L ∈ S, symbolEvalProbability color (latinCellValue xy L) z at h
  calc
    _ = _ := h
    _ = _ := by ring

end LatinonEntropy

#print axioms LatinonEntropy.symbol_mixture_moment
#print axioms LatinonEntropy.symbol_mixture_marginal_eq
