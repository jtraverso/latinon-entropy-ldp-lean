module

public import WeightedLabelErrors

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def labelRoundingCost {n r s t : ℕ} (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (C : Fin t → Fin n × Fin n → ℝ) (omega : (Fin n → Fin r) × (Fin n → Fin s)) : ℝ :=
  (∑ z : (Fin r × Fin s) × Fin t, (labelBlockError p q (C z.2) z.1.1 z.1.2 omega)^2)+
  (∑ a : Fin r, (labelClassError p a omega.1)^2)+(∑ b : Fin s, (labelClassError q b omega.2)^2)

theorem labelRoundingCost_nonneg {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (C : Fin t → Fin n × Fin n → ℝ)
    (omega : (Fin n → Fin r) × (Fin n → Fin s)) : 0 ≤ labelRoundingCost p q C omega := by
  unfold labelRoundingCost
  positivity

/-- The actual single cost simultaneously controls all table coordinates
and all row/column class proportions. -/
theorem pairedLabel_rounding_cost_le {n r s t : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hq : ∀ y b, 0 ≤ q y b)
    (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (C : Fin t → Fin n × Fin n → ℝ) (hC : ∀ k xy, 0 ≤ C k xy ∧ C k xy ≤ 1) :
    pairedLabelMean p q (labelRoundingCost p q C) ≤
      (2*(r : ℝ)*(s : ℝ)*(t : ℝ)+(r : ℝ)+(s : ℝ))/(n : ℝ) := by
  have hb : finiteExpectation (pairedLabelWeight p q)
      (fun omega => ∑ z : (Fin r × Fin s) × Fin t,
        (labelBlockError p q (C z.2) z.1.1 z.1.2 omega)^2) ≤
      ∑ _z : (Fin r × Fin s) × Fin t, (2 : ℝ)/(n : ℝ) := by
    rw [finiteExpectation_sum]
    exact sum_le_sum (fun z _ => pairedLabel_block_error_sq_le hn p q hp hq hpt hqt
      (C z.2) (hC z.2) z.1.1 z.1.2)
  have hr : finiteExpectation (pairedLabelWeight p q)
      (fun omega => ∑ a : Fin r, (labelClassError p a omega.1)^2) ≤
      ∑ _a : Fin r, (1 : ℝ)/(n : ℝ) := by
    rw [finiteExpectation_sum]
    exact sum_le_sum (fun a _ => pairedLabel_row_error_sq_le hn p q hp hpt hqt a)
  have hc : finiteExpectation (pairedLabelWeight p q)
      (fun omega => ∑ b : Fin s, (labelClassError q b omega.2)^2) ≤
      ∑ _b : Fin s, (1 : ℝ)/(n : ℝ) := by
    rw [finiteExpectation_sum]
    exact sum_le_sum (fun b _ => pairedLabel_col_error_sq_le hn p q hq hpt hqt b)
  unfold pairedLabelMean labelRoundingCost
  rw [finiteExpectation_add,finiteExpectation_add]
  calc
    _ ≤ (∑ _z : (Fin r × Fin s) × Fin t, (2 : ℝ)/(n : ℝ))+
        (∑ _a : Fin r, (1 : ℝ)/(n : ℝ))+(∑ _b : Fin s, (1 : ℝ)/(n : ℝ)) :=
      add_le_add (add_le_add hb hr) hc
    _ = _ := by
      simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,nsmul_eq_mul]
      ring

theorem labelBlockError_sq_le_cost {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (C : Fin t → Fin n × Fin n → ℝ)
    (omega : (Fin n → Fin r) × (Fin n → Fin s)) (a : Fin r) (b : Fin s) (k : Fin t) :
    (labelBlockError p q (C k) a b omega)^2 ≤ labelRoundingCost p q C omega := by
  have hs := single_le_sum
    (f := fun z : (Fin r × Fin s) × Fin t => (labelBlockError p q (C z.2) z.1.1 z.1.2 omega)^2)
    (fun _ _ => sq_nonneg _) (mem_univ ((a,b),k))
  have hr : (0 : ℝ) ≤ ∑ i : Fin r, (labelClassError p i omega.1)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0 : ℝ) ≤ ∑ j : Fin s, (labelClassError q j omega.2)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  unfold labelRoundingCost
  linarith only [hs,hr,hc]

theorem labelRowError_sq_le_cost {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (C : Fin t → Fin n × Fin n → ℝ)
    (omega : (Fin n → Fin r) × (Fin n → Fin s)) (a : Fin r) :
    (labelClassError p a omega.1)^2 ≤ labelRoundingCost p q C omega := by
  have hs := single_le_sum (f := fun i : Fin r => (labelClassError p i omega.1)^2)
    (fun _ _ => sq_nonneg _) (mem_univ a)
  have hb : (0 : ℝ) ≤ ∑ z : (Fin r × Fin s) × Fin t,
      (labelBlockError p q (C z.2) z.1.1 z.1.2 omega)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0 : ℝ) ≤ ∑ j : Fin s, (labelClassError q j omega.2)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  unfold labelRoundingCost
  linarith only [hs,hb,hc]

theorem labelColError_sq_le_cost {n r s t : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ) (C : Fin t → Fin n × Fin n → ℝ)
    (omega : (Fin n → Fin r) × (Fin n → Fin s)) (b : Fin s) :
    (labelClassError q b omega.2)^2 ≤ labelRoundingCost p q C omega := by
  have hs := single_le_sum (f := fun j : Fin s => (labelClassError q j omega.2)^2)
    (fun _ _ => sq_nonneg _) (mem_univ b)
  have hb : (0 : ℝ) ≤ ∑ z : (Fin r × Fin s) × Fin t,
      (labelBlockError p q (C z.2) z.1.1 z.1.2 omega)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hr : (0 : ℝ) ≤ ∑ i : Fin r, (labelClassError p i omega.1)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  unfold labelRoundingCost
  linarith only [hs,hb,hr]

end LatinonEntropy
