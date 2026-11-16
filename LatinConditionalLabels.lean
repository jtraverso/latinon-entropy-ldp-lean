module

public import LatinWeightedReveal
public import LatinBlockingCells
public import FiniteLabelThresholds
public import FinitePriorityKey

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def fixedCellLabels {n M : ℕ} (xy : LatinCell n) (t : Fin M)
    (rest : {k : LatinCell n // k ≠ xy} → Fin M) : LatinCell n → Fin M :=
  (Equiv.funSplitAt xy (Fin M)).symm (t,rest)

theorem fixedCellLabels_self {n M : ℕ} (xy : LatinCell n) (t : Fin M)
    (rest : {k : LatinCell n // k ≠ xy} → Fin M) : fixedCellLabels xy t rest xy = t := by
  simp [fixedCellLabels,Equiv.funSplitAt_symm_apply]

theorem fixedCellLabels_other {n M : ℕ} (xy : LatinCell n) (t : Fin M)
    (rest : {k : LatinCell n // k ≠ xy} → Fin M) (k : LatinCell n) (hk : k ≠ xy) :
    fixedCellLabels xy t rest k = rest ⟨k,hk⟩ := by
  simp [fixedCellLabels,Equiv.funSplitAt_symm_apply,hk]

theorem latin_alternative_conditional_mean_le {n M : ℕ} (L : LatinArray n)
    (xy : LatinCell n) (z : Fin n) (hz : z ≠ latinCellValue xy L)
    (t : Fin M) (w : ℝ) (hw : 0 ≤ w) :
    finiteMean (fun rest : {k : LatinCell n // k ≠ xy} → Fin M =>
      if finitePriorityKey (fixedCellLabels xy t rest) xy ≤
          finitePriorityKey (fixedCellLabels xy t rest) (xy.1,latinRowOwner L xy z) ∧
        finitePriorityKey (fixedCellLabels xy t rest) xy ≤
          finitePriorityKey (fixedCellLabels xy t rest) (latinColOwner L xy z,xy.2)
      then w else 0) ≤ (((M : ℝ)-t)/M)^2*w := by
  have hb := latin_alternative_blockers L xy z hz
  let u : {k : LatinCell n // k ≠ xy} := ⟨(xy.1,latinRowOwner L xy z),hb.1⟩
  let v : {k : LatinCell n // k ≠ xy} := ⟨(latinColOwner L xy z,xy.2),hb.2.1⟩
  have huv : u ≠ v := by intro he; exact hb.2.2 (congrArg Subtype.val he)
  have hpoint : ∀ rest : {k : LatinCell n // k ≠ xy} → Fin M,
      (if finitePriorityKey (fixedCellLabels xy t rest) xy ≤
          finitePriorityKey (fixedCellLabels xy t rest) (xy.1,latinRowOwner L xy z) ∧
        finitePriorityKey (fixedCellLabels xy t rest) xy ≤
          finitePriorityKey (fixedCellLabels xy t rest) (latinColOwner L xy z,xy.2)
      then w else 0) ≤ (if t ≤ rest u ∧ t ≤ rest v then w else 0) := by
    intro rest
    split_ifs with hord hlabel hlabel
    · exact le_rfl
    · have h1 := label_le_of_finitePriorityKey_le (fixedCellLabels xy t rest) xy _ hord.1
      have h2 := label_le_of_finitePriorityKey_le (fixedCellLabels xy t rest) xy _ hord.2
      rw [fixedCellLabels_self,fixedCellLabels_other xy t rest _ hb.1] at h1
      rw [fixedCellLabels_self,fixedCellLabels_other xy t rest _ hb.2.1] at h2
      exact False.elim (hlabel ⟨h1,h2⟩)
    · exact hw
    · exact le_rfl
  exact (finiteMean_mono hpoint).trans_eq (finiteMean_two_label_thresholds u v huv t w)

theorem latin_conditional_remaining_mean_le {n M : ℕ} (L : LatinArray n)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n) (t : Fin M)
    (hr : ∀ z, 0 ≤ r xy z) (hrow : ∑ z, r xy z = 1) :
    finiteMean (fun rest : {k : LatinCell n // k ≠ xy} → Fin M =>
      latinRemainingReference (finitePriorityKey (fixedCellLabels xy t rest)) r xy L) ≤
        r xy (latinCellValue xy L)+(((M : ℝ)-t)/M)^2 := by
  let : Nonempty (Fin M) := ⟨t⟩
  let T := fun (z : Fin n) (rest : {k : LatinCell n // k ≠ xy} → Fin M) =>
    if finitePriorityKey (fixedCellLabels xy t rest) xy ≤
        finitePriorityKey (fixedCellLabels xy t rest) (xy.1,latinRowOwner L xy z) ∧
      finitePriorityKey (fixedCellLabels xy t rest) xy ≤
        finitePriorityKey (fixedCellLabels xy t rest) (latinColOwner L xy z,xy.2)
    then r xy z else 0
  have hfun : (fun rest : {k : LatinCell n // k ≠ xy} → Fin M =>
      latinRemainingReference (finitePriorityKey (fixedCellLabels xy t rest)) r xy L) =
      (fun rest => ∑ z, T z rest) := by
    funext rest
    simp only [latinRemainingReference,sum_filter,T]
  rw [hfun,finiteMean_sum]
  have hmean : ∀ z : Fin n, finiteMean (T z) ≤
      (if z = latinCellValue xy L then r xy z else 0)+(((M : ℝ)-t)/M)^2*r xy z := by
    intro z
    split_ifs with hz
    · have hc : finiteMean (T z) ≤ r xy z := by
        calc
          _ ≤ finiteMean (fun _ : {k : LatinCell n // k ≠ xy} → Fin M => r xy z) := by
            apply finiteMean_mono
            intro rest
            dsimp only [T]
            split_ifs
            · exact le_rfl
            · exact hr z
          _ = _ := finiteMean_const _
      linarith only [hc,mul_nonneg (sq_nonneg (((M : ℝ)-t)/M)) (hr z)]
    · simpa only [T,zero_add] using latin_alternative_conditional_mean_le L xy z hz t (r xy z) (hr z)
  calc
    _ ≤ ∑ z : Fin n, ((if z = latinCellValue xy L then r xy z else 0)+
        (((M : ℝ)-t)/M)^2*r xy z) := sum_le_sum (fun z _ => hmean z)
    _ = _ := by rw [sum_add_distrib,← mul_sum,hrow,mul_one]; simp

end LatinonEntropy

#print axioms LatinonEntropy.latin_alternative_conditional_mean_le
#print axioms LatinonEntropy.latin_conditional_remaining_mean_le
