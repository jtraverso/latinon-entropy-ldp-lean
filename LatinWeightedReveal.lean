module

public import LatinRevealAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def latinRemainingReference {n : ℕ} (key : LatinCell n → ℕ)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n) (L : LatinArray n) : ℝ :=
  ∑ z ∈ univ.filter (fun z => key xy ≤ key (xy.1,latinRowOwner L xy z) ∧
    key xy ≤ key (latinColOwner L xy z,xy.2)), r xy z

theorem availableReference_latin_le {n : ℕ} (S : Finset (LatinArray n))
    (key : LatinCell n → ℕ) (r : LatinCell n → Fin n → ℝ)
    (hr : ∀ xy z, 0 ≤ r xy z) (xy : LatinCell n) (L : LatinArray n) :
    availableReference S univ key latinCellValue r xy L ≤ latinRemainingReference key r xy L := by
  unfold availableReference latinRemainingReference
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hr xy z)
  intro z hz
  exact mem_filter.mpr ⟨mem_univ _,latin_reveal_symbol_orders S key L xy z hz⟩

theorem availableReference_latin_pos {n : ℕ} (S : Finset (LatinArray n))
    (key : LatinCell n → ℕ) (r : LatinCell n → Fin n → ℝ)
    (hr : ∀ xy z, 0 ≤ r xy z) (xy : LatinCell n) (L : LatinArray n) (hL : L ∈ S)
    (hentry : 0 < r xy (latinCellValue xy L)) :
    0 < availableReference S univ key latinCellValue r xy L := by
  have hself : L ∈ revealFibre S univ key latinCellValue xy L := by simp [revealFibre,hL]
  have hm := mem_image_of_mem (latinCellValue xy) hself
  exact hentry.trans_le (single_le_sum (fun z _ => hr xy z) hm)

/-- An arbitrary positively weighted finite family of actual Latin arrays.
The reference distribution is retained in both row and column availability. -/
theorem latin_weighted_revealing_bound {n : ℕ} (S : Finset (LatinArray n))
    (hS : S.Nonempty) (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 < w L)
    (key : LatinCell n → ℕ) (hkey : Function.Injective key)
    (r : LatinCell n → Fin n → ℝ) (hr : ∀ xy z, 0 ≤ r xy z)
    (hentry : ∀ xy L, L ∈ S → 0 < r xy (latinCellValue xy L)) :
    weightedFamilyEntropy S w ≤ ∑ L ∈ S, w L*∑ xy : LatinCell n,
      (Real.log (latinRemainingReference key r xy L)-Real.log (r xy (latinCellValue xy L))) := by
  have hdet : ∀ L ∈ S, ∀ K ∈ S, (∀ xy ∈ (univ : Finset (LatinCell n)),
      latinCellValue xy L = latinCellValue xy K) → L = K := by
    intro L _ K _ he
    apply Subtype.ext
    funext x y
    exact he (x,y) (mem_univ _)
  have hchain := weighted_chain_bound key latinCellValue w r univ S
    (fun _ _ _ _ he => hkey he) hdet hS hw (fun xy _ L hL => hentry xy L hL)
  apply hchain.trans
  apply sum_le_sum
  intro L hL
  apply mul_le_mul_of_nonneg_left ?_ (hw L hL).le
  apply sum_le_sum
  intro xy _
  exact sub_le_sub_right (Real.log_le_log
    (availableReference_latin_pos S key r hr xy L hL (hentry xy L hL))
    (availableReference_latin_le S key r hr xy L)) _

end LatinonEntropy

#print axioms LatinonEntropy.latin_weighted_revealing_bound
