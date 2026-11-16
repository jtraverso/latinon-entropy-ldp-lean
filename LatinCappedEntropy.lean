module

public import LatinMarginalRevealing

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset Filter Topology
open scoped Classical

theorem latin_priority_log_mean_le {n M : ℕ} (hM : 0 < M) (L : LatinArray n)
    (r : LatinCell n → Fin n → ℝ) (xy : LatinCell n)
    (hr : ∀ z, 0 ≤ r xy z) (hrow : ∑ z, r xy z = 1)
    (hentry : 0 < r xy (latinCellValue xy L))
    (hcap : r xy (latinCellValue xy L) ≤ (1/(M : ℝ))^2) :
    finiteMean (fun lam : LatinCell n → Fin M =>
      Real.log (latinRemainingReference (finitePriorityKey lam) r xy L)) ≤
        -2+2*permanentCapError 1 M/(M : ℝ) := by
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h := latin_finite_priority_log_sum hM L r xy hr hrow hentry hcap
  calc
    _ ≤ (-2*(M : ℝ)+2*permanentCapError 1 M)/(M : ℝ) :=
      (le_div_iff₀ hMR).mpr (by nlinarith only [h])
    _ = _ := by field_simp [hMR.ne']

/-- An actual normalized finite law on Latin arrays, with its own
marginals as references. No conditional entropy estimate is assumed. -/
theorem latin_capped_marginal_entropy_upper {n M : ℕ} (hM : 0 < M)
    (S : Finset (LatinArray n)) (hS : S.Nonempty) (w : LatinArray n → ℝ)
    (hw : ∀ L ∈ S, 0 < w L) (htotal : ∑ L ∈ S, w L = 1)
    (hcap : ∀ xy z, latinFamilyMarginal S w xy z ≤ (1/(M : ℝ))^2) :
    weightedFamilyEntropy S w ≤ latinMarginalEntropy S w-2*(n : ℝ)^2+
      (n : ℝ)^2*(2*permanentCapError 1 M/(M : ℝ)) := by
  let : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  let k := -2+2*permanentCapError 1 M/(M : ℝ)
  have hr : ∀ xy z, 0 ≤ latinFamilyMarginal S w xy z := fun xy z =>
    latinFamilyMarginal_nonneg S w (fun L hL => (hw L hL).le) xy z
  have hrow : ∀ xy, ∑ z, latinFamilyMarginal S w xy z = 1 := by
    intro xy
    rw [latinFamilyMarginal_total,htotal]
  have hcell : ∀ L ∈ S, ∀ xy : LatinCell n,
      finiteMean (fun lam : LatinCell n → Fin M => Real.log
        (latinRemainingReference (finitePriorityKey lam) (latinFamilyMarginal S w) xy L)) ≤ k := by
    intro L hL xy
    exact latin_priority_log_mean_le hM L (latinFamilyMarginal S w) xy (hr xy) (hrow xy)
      ((hw L hL).trans_le (latinFamilyMarginal_self_ge S w (fun K hK => (hw K hK).le) xy L hL))
      (hcap xy (latinCellValue xy L))
  have hmean := finiteMean_mono (fun lam : LatinCell n → Fin M =>
    latin_marginal_revealing_bound S hS w hw (finitePriorityKey lam) (finitePriorityKey_injective lam))
  simp only [finiteMean_const,finiteMean_sum,finiteMean_mul] at hmean
  have hbound : (∑ L ∈ S, w L*∑ xy : LatinCell n,
      finiteMean (fun lam : LatinCell n → Fin M => Real.log
        (latinRemainingReference (finitePriorityKey lam) (latinFamilyMarginal S w) xy L))) ≤
      (n : ℝ)^2*k := by
    calc
      _ ≤ ∑ L ∈ S, w L*∑ _xy : LatinCell n, k := by
        apply sum_le_sum
        intro L hL
        exact mul_le_mul_of_nonneg_left (sum_le_sum (fun xy _ => hcell L hL xy)) (hw L hL).le
      _ = _ := by
        have hcells : (∑ _xy : LatinCell n, k) = (n : ℝ)^2*k := by
          simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
          ring
        simp_rw [hcells]
        rw [← sum_mul,htotal,one_mul]
  dsimp only [k] at hbound
  nlinarith only [hmean,hbound]

/-- A single marginal threshold suffices for every order and every finite
normalized Latin law, at any prescribed positive entropy error. -/
theorem exists_uniform_latin_marginal_entropy_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℕ, 0 < M ∧ ∀ (n : ℕ) (S : Finset (LatinArray n)) (w : LatinArray n → ℝ),
      S.Nonempty → (∀ L ∈ S, 0 < w L) → (∑ L ∈ S, w L = 1) →
      (∀ xy z, latinFamilyMarginal S w xy z ≤ (1/(M : ℝ))^2) →
        weightedFamilyEntropy S w ≤ latinMarginalEntropy S w-2*(n : ℝ)^2+eta*(n : ℝ)^2 := by
  have hs := (tendsto_order.mp latin_label_cap_error_tendsto_zero).2 eta heta
  obtain ⟨M,hsmall,hM⟩ := (hs.and (eventually_ge_atTop 1)).exists
  have hMpos : 0 < M := by omega
  refine ⟨M,hMpos,?_⟩
  intro n S w hS hw htotal hcap
  have h := latin_capped_marginal_entropy_upper hMpos S hS w hw htotal hcap
  have he := mul_le_mul_of_nonneg_left hsmall.le (sq_nonneg (n : ℝ))
  nlinarith only [h,he]

end LatinonEntropy

#print axioms LatinonEntropy.latin_priority_log_mean_le
#print axioms LatinonEntropy.latin_capped_marginal_entropy_upper
#print axioms LatinonEntropy.exists_uniform_latin_marginal_entropy_threshold
