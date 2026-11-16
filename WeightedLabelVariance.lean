module

public import WeightedLabelCovariance
public import WeightedLabelMarginals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def labelClassCount {I A : Type*} [Fintype I] (a : A) (ell : I → A) : ℝ :=
  ∑ i, labelHit i a ell

def labelBlockCount {I J A B : Type*} [Fintype I] [Fintype J]
    (C : I × J → ℝ) (a : A) (b : B) (omega : (I → A) × (J → B)) : ℝ :=
  ∑ xy, C xy*pairedCellHit xy a b omega

def fractionalBlockCount {I J A B : Type*} [Fintype I] [Fintype J]
    (p : I → A → ℝ) (q : J → B → ℝ) (C : I × J → ℝ) (a : A) (b : B) : ℝ :=
  ∑ xy, C xy*(p xy.1 a*q xy.2 b)

theorem productLabelMean_class_count {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (a : A) :
    productLabelMean p (labelClassCount a) = ∑ i, p i a := by
  change finiteExpectation (productLabelWeight p) (fun ell => ∑ i, labelHit i a ell) = _
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  exact productLabelMean_hit p hp i a

theorem pairedLabelMean_block_count {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ j, ∑ b, q j b = 1)
    (C : I × J → ℝ) (a : A) (b : B) :
    pairedLabelMean p q (labelBlockCount C a b) = fractionalBlockCount p q C a b := by
  change finiteExpectation (pairedLabelWeight p q)
    (fun omega => ∑ xy, C xy*pairedCellHit xy a b omega) = _
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro xy _
  rw [finiteExpectation_mul_left]
  exact congrArg (fun t => C xy*t) (pairedLabelMean_cell p q hp hq xy a b)

theorem productLabel_class_variance_le {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : ∀ x a, 0 ≤ p x a) (htotal : ∀ x, ∑ a, p x a = 1)
    (a : Fin r) : finiteVariance (productLabelWeight p) (labelClassCount a) ≤ (n : ℝ) := by
  change finiteVariance (productLabelWeight p) (fun ell => ∑ x, labelHit x a ell) ≤ _
  have he : finiteVariance (productLabelWeight p) (fun ell => ∑ x, labelHit x a ell) =
      ∑ x : Fin n, ∑ y : Fin n, finiteCovariance (productLabelWeight p) (labelHit x a) (labelHit y a) := by
    simpa only [one_mul] using finiteVariance_sum (productLabelWeight p)
      (productLabelWeight_total p htotal) univ (fun _ : Fin n => (1 : ℝ)) (fun x => labelHit x a)
  rw [he]
  calc
    _ ≤ ∑ x : Fin n, ∑ y : Fin n, (if x = y then (1 : ℝ) else 0) :=
      sum_le_sum (fun x _ => sum_le_sum (fun y _ => productLabel_covariance_le p hp htotal x y a))
    _ = _ := by simp

theorem cell_coordinate_pair_sum (n : ℕ) :
    (∑ xy : Fin n × Fin n, ∑ uv : Fin n × Fin n,
      ((if xy.1 = uv.1 then (1 : ℝ) else 0)+(if xy.2 = uv.2 then 1 else 0))) = 2*(n : ℝ)^3 := by
  have hrow : ∀ xy : Fin n × Fin n,
      (∑ uv : Fin n × Fin n, if xy.1 = uv.1 then (1 : ℝ) else 0) = (n : ℝ) := by
    intro xy
    rw [Fintype.sum_prod_type,sum_comm]
    simp
  have hcol : ∀ xy : Fin n × Fin n,
      (∑ uv : Fin n × Fin n, if xy.2 = uv.2 then (1 : ℝ) else 0) = (n : ℝ) := by
    intro xy
    rw [Fintype.sum_prod_type]
    simp
  simp only [sum_add_distrib,hrow,hcol,sum_const,card_univ,Fintype.card_prod,
    Fintype.card_fin,Nat.cast_mul,nsmul_eq_mul]
  ring

/-- The block variance is derived from the actual product law and the
two coordinate-overlap sums. Coefficients may be any values in [0,1]. -/
theorem pairedLabel_block_variance_le {n r s : ℕ}
    (p : Fin n → Fin r → ℝ) (q : Fin n → Fin s → ℝ)
    (hp : ∀ x a, 0 ≤ p x a) (hq : ∀ y b, 0 ≤ q y b)
    (hpt : ∀ x, ∑ a, p x a = 1) (hqt : ∀ y, ∑ b, q y b = 1)
    (C : Fin n × Fin n → ℝ) (hC : ∀ xy, 0 ≤ C xy ∧ C xy ≤ 1) (a : Fin r) (b : Fin s) :
    finiteVariance (pairedLabelWeight p q) (labelBlockCount C a b) ≤ 2*(n : ℝ)^3 := by
  change finiteVariance (pairedLabelWeight p q) (fun omega => ∑ xy, C xy*pairedCellHit xy a b omega) ≤ _
  rw [finiteVariance_sum _ (pairedLabelWeight_total p q hpt hqt)]
  calc
    _ ≤ ∑ xy : Fin n × Fin n, ∑ uv : Fin n × Fin n,
        ((if xy.1 = uv.1 then (1 : ℝ) else 0)+(if xy.2 = uv.2 then 1 else 0)) := by
      apply sum_le_sum
      intro xy _
      apply sum_le_sum
      intro uv _
      have hcv := pairedCell_covariance_le p q hp hq hpt hqt xy uv a b
      have hc0 : 0 ≤ C xy*C uv := mul_nonneg (hC xy).1 (hC uv).1
      have hc1 : C xy*C uv ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hC xy).2 (hC uv).2 (hC uv).1 (by norm_num : (0 : ℝ) ≤ 1)
      have hd : (0 : ℝ) ≤ (if xy.1 = uv.1 then 1 else 0)+(if xy.2 = uv.2 then 1 else 0) := by
        split_ifs <;> norm_num
      calc
        _ ≤ C xy*C uv*((if xy.1 = uv.1 then 1 else 0)+(if xy.2 = uv.2 then 1 else 0)) :=
          mul_le_mul_of_nonneg_left hcv hc0
        _ ≤ 1*((if xy.1 = uv.1 then 1 else 0)+(if xy.2 = uv.2 then 1 else 0)) :=
          mul_le_mul_of_nonneg_right hc1 hd
        _ = _ := one_mul _
    _ = _ := cell_coordinate_pair_sum n

end LatinonEntropy
