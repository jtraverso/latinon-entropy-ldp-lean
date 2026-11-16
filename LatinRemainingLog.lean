module

public import LatinConditionalLabels
public import LatinLabelCap

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_remaining_reference_ge_actual {n : ℕ} (key : LatinCell n → ℕ)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n) (L : LatinArray n)
    (hr : ∀ z, 0 ≤ r xy z) :
    r xy (latinCellValue xy L) ≤ latinRemainingReference key r xy L := by
  unfold latinRemainingReference
  apply Finset.single_le_sum (f := r xy) (fun z _ => hr z)
  simp only [mem_filter,mem_univ,true_and]
  obtain ⟨hrow,hcol⟩ := latin_chosen_symbol_owners L xy
  rw [hrow,hcol]
  simp

theorem latin_conditional_remaining_log_le {n M : ℕ} (L : LatinArray n)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n) (t : Fin M)
    (hr : ∀ z, 0 ≤ r xy z) (hrow : ∑ z, r xy z = 1)
    (hentry : 0 < r xy (latinCellValue xy L)) (s : ℝ)
    (hcap : r xy (latinCellValue xy L) ≤ s) :
    finiteMean (fun rest : {k : LatinCell n // k ≠ xy} → Fin M =>
      Real.log (latinRemainingReference (finitePriorityKey (fixedCellLabels xy t rest)) r xy L)) ≤
        Real.log (s+(((M : ℝ)-t)/M)^2) := by
  let : Nonempty (Fin M) := ⟨t⟩
  let F := fun rest : {k : LatinCell n // k ≠ xy} → Fin M =>
    latinRemainingReference (finitePriorityKey (fixedCellLabels xy t rest)) r xy L
  have hf : ∀ rest, 0 < F rest := fun rest =>
    hentry.trans_le (latin_remaining_reference_ge_actual _ r xy L hr)
  have hlow : r xy (latinCellValue xy L) ≤ finiteMean F := by
    calc
      _ = finiteMean (fun _ : {k : LatinCell n // k ≠ xy} → Fin M =>
        r xy (latinCellValue xy L)) := (finiteMean_const _).symm
      _ ≤ _ := finiteMean_mono (fun _ => latin_remaining_reference_ge_actual _ r xy L hr)
  have hmean := latin_conditional_remaining_mean_le L r xy t hr hrow
  exact (finiteMean_log_le F hf).trans
    (Real.log_le_log (hentry.trans_le hlow) (hmean.trans (add_le_add hcap le_rfl)))

theorem latin_finite_priority_log_sum {n M : ℕ} (hM : 0 < M) (L : LatinArray n)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n)
    (hr : ∀ z, 0 ≤ r xy z) (hrow : ∑ z, r xy z = 1)
    (hentry : 0 < r xy (latinCellValue xy L))
    (hcap : r xy (latinCellValue xy L) ≤ (1/(M : ℝ))^2) :
    (M : ℝ)*finiteMean (fun lam : LatinCell n → Fin M =>
      Real.log (latinRemainingReference (finitePriorityKey lam) r xy L)) ≤
        -2*(M : ℝ)+2*permanentCapError 1 M := by
  let : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  rw [finiteMean_split xy]
  have hmean := finiteMean_mono (fun t : Fin M =>
    latin_conditional_remaining_log_le L r xy t hr hrow hentry ((1/(M : ℝ))^2) hcap)
  have hscale := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (α := ℝ) M)
  exact hscale.trans (finite_label_quadratic_cap_sum M hM ((1/(M : ℝ))^2) (sq_nonneg _) le_rfl)

end LatinonEntropy

#print axioms LatinonEntropy.latin_remaining_reference_ge_actual
#print axioms LatinonEntropy.latin_conditional_remaining_log_le
#print axioms LatinonEntropy.latin_finite_priority_log_sum
