module

public import WeightedLabelVariance

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def labelClassError {n r : ℕ} (p : Fin n → Fin r → ℝ) (a : Fin r) (ell : Fin n → Fin r) : ℝ :=
  labelClassCount a ell/(n : ℝ)-(∑ x, p x a)/(n : ℝ)

def labelBlockError {n r s : ℕ} (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (C : Fin n × Fin n → ℝ) (a : Fin r) (b : Fin s)
    (omega : (Fin n → Fin r) × (Fin n → Fin s)) : ℝ :=
  labelBlockCount C a b omega/(n : ℝ)^2-fractionalBlockCount p q C a b/(n : ℝ)^2

theorem finiteExpectation_centered_div {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun omega => (X omega/c-finiteExpectation w X/c)^2) =
      finiteVariance w X/c^2 := by
  calc
    _ = finiteExpectation w (fun omega => (X omega-finiteExpectation w X)^2/c^2) := by
      apply finiteExpectation_congr
      intro omega
      rw [← sub_div,div_pow]
    _ = _ := finiteExpectation_div w _ (c^2)

theorem productLabel_class_error_sq_le {n r : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (hp : ∀ x a, 0 ≤ p x a) (htotal : ∀ x, ∑ a, p x a = 1)
    (a : Fin r) :
    productLabelMean p (fun ell => (labelClassError p a ell)^2) ≤ 1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm := productLabelMean_class_count p htotal a
  unfold labelClassError
  rw [← hm]
  change finiteExpectation (productLabelWeight p)
    (fun ell => (labelClassCount a ell/(n : ℝ)-
      finiteExpectation (productLabelWeight p) (labelClassCount a)/(n : ℝ))^2) ≤ _
  rw [finiteExpectation_centered_div]
  calc
    _ ≤ (n : ℝ)/(n : ℝ)^2 := div_le_div_of_nonneg_right
      (productLabel_class_variance_le p hp htotal a) (sq_nonneg _)
    _ = _ := by
      apply (div_eq_div_iff (pow_ne_zero 2 hnR.ne') hnR.ne').mpr
      ring

theorem pairedLabel_row_error_sq_le {n r s : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (a : Fin r) :
    pairedLabelMean p q (fun omega => (labelClassError p a omega.1)^2) ≤ 1/(n : ℝ) := by
  rw [pairedLabelMean_fst p q hqt (fun ell => (labelClassError p a ell)^2)]
  exact productLabel_class_error_sq_le hn p hp hpt a

theorem pairedLabel_col_error_sq_le {n r s : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hq : ∀ y b, 0 ≤ q y b) (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (b : Fin s) :
    pairedLabelMean p q (fun omega => (labelClassError q b omega.2)^2) ≤ 1/(n : ℝ) := by
  rw [pairedLabelMean_snd p q hpt (fun m => (labelClassError q b m)^2)]
  exact productLabel_class_error_sq_le hn q hq hqt b

theorem pairedLabel_block_error_sq_le {n r s : ℕ} (hn : 0 < n)
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hq : ∀ y b, 0 ≤ q y b)
    (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (C : Fin n × Fin n → ℝ) (hC : ∀ xy, 0 ≤ C xy ∧ C xy ≤ 1) (a : Fin r) (b : Fin s) :
    pairedLabelMean p q (fun omega => (labelBlockError p q C a b omega)^2) ≤ 2/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm := pairedLabelMean_block_count p q hpt hqt C a b
  unfold labelBlockError
  rw [← hm]
  change finiteExpectation (pairedLabelWeight p q)
    (fun omega => (labelBlockCount C a b omega/(n : ℝ)^2-
      finiteExpectation (pairedLabelWeight p q) (labelBlockCount C a b)/(n : ℝ)^2)^2) ≤ _
  rw [finiteExpectation_centered_div]
  calc
    _ ≤ (2*(n : ℝ)^3)/((n : ℝ)^2)^2 := div_le_div_of_nonneg_right
      (pairedLabel_block_variance_le p q hp hq hpt hqt C hC a b) (sq_nonneg _)
    _ = _ := by
      apply (div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hnR.ne')) hnR.ne').mpr
      ring

end LatinonEntropy
