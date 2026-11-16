module

public import FiniteLabelMoments

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def pairedLabelWeight {I J A B : Type*} [Fintype I] [Fintype J]
    (p : I → A → ℝ) (q : J → B → ℝ) (omega : (I → A) × (J → B)) : ℝ :=
  productLabelWeight p omega.1*productLabelWeight q omega.2

def pairedLabelMean {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (X : ((I → A) × (J → B)) → ℝ) : ℝ :=
  finiteExpectation (pairedLabelWeight p q) X

def pairedCellHit {I J A B : Type*} (xy : I × J) (a : A) (b : B)
    (omega : (I → A) × (J → B)) : ℝ :=
  labelHit xy.1 a omega.1*labelHit xy.2 b omega.2

theorem pairedLabelWeight_nonneg {I J A B : Type*} [Fintype I] [Fintype J]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ j b, 0 ≤ q j b) (omega : (I → A) × (J → B)) :
    0 ≤ pairedLabelWeight p q omega :=
  mul_nonneg (productLabelWeight_nonneg p hp omega.1) (productLabelWeight_nonneg q hq omega.2)

theorem pairedLabelWeight_total {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ j, ∑ b, q j b = 1) :
    (∑ omega : (I → A) × (J → B), pairedLabelWeight p q omega) = 1 := by
  simp only [pairedLabelWeight,Fintype.sum_prod_type,← mul_sum,productLabelWeight_total q hq,mul_one]
  exact productLabelWeight_total p hp

theorem pairedLabelMean_separable {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (F : (I → A) → ℝ) (G : (J → B) → ℝ) :
    pairedLabelMean p q (fun omega => F omega.1*G omega.2) = productLabelMean p F*productLabelMean q G := by
  simp only [pairedLabelMean,productLabelMean,finiteExpectation,pairedLabelWeight,
    Fintype.sum_prod_type,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ell _
  apply sum_congr rfl
  intro m _
  ring

theorem pairedCellHit_nonneg {I J A B : Type*} (xy : I × J) (a : A) (b : B)
    (omega : (I → A) × (J → B)) : 0 ≤ pairedCellHit xy a b omega :=
  mul_nonneg (labelHit_nonneg xy.1 a omega.1) (labelHit_nonneg xy.2 b omega.2)

theorem pairedCellHit_le_one {I J A B : Type*} (xy : I × J) (a : A) (b : B)
    (omega : (I → A) × (J → B)) : pairedCellHit xy a b omega ≤ 1 := by
  unfold pairedCellHit labelHit
  split_ifs <;> norm_num

theorem pairedLabelMean_cell {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ j, ∑ b, q j b = 1) (xy : I × J) (a : A) (b : B) :
    pairedLabelMean p q (pairedCellHit xy a b) = p xy.1 a*q xy.2 b := by
  change pairedLabelMean p q (fun omega => labelHit xy.1 a omega.1*labelHit xy.2 b omega.2) = _
  rw [pairedLabelMean_separable,productLabelMean_hit p hp,productLabelMean_hit q hq]

theorem pairedLabelMean_cell_pair {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ j, ∑ b, q j b = 1)
    (xy uv : I × J) (a : A) (b : B) :
    pairedLabelMean p q (fun omega => pairedCellHit xy a b omega*pairedCellHit uv a b omega) =
      (if xy.1 = uv.1 then p xy.1 a else p xy.1 a*p uv.1 a)*
      (if xy.2 = uv.2 then q xy.2 b else q xy.2 b*q uv.2 b) := by
  calc
    _ = pairedLabelMean p q (fun omega =>
        (labelHit xy.1 a omega.1*labelHit uv.1 a omega.1)*
        (labelHit xy.2 b omega.2*labelHit uv.2 b omega.2)) := by
      apply finiteExpectation_congr
      intro omega
      unfold pairedCellHit
      ring
    _ = productLabelMean p (fun ell => labelHit xy.1 a ell*labelHit uv.1 a ell)*
        productLabelMean q (fun m => labelHit xy.2 b m*labelHit uv.2 b m) :=
      pairedLabelMean_separable p q (fun ell => labelHit xy.1 a ell*labelHit uv.1 a ell)
        (fun m => labelHit xy.2 b m*labelHit uv.2 b m)
    _ = _ := by rw [productLabelMean_hit_pair p hp,productLabelMean_hit_pair q hq]

theorem pairedLabelMean_cell_pair_le_one {I J A B : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [Fintype B]
    (p : I → A → ℝ) (q : J → B → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hq : ∀ j b, 0 ≤ q j b)
    (hpt : ∀ i, ∑ a, p i a = 1) (hqt : ∀ j, ∑ b, q j b = 1)
    (xy uv : I × J) (a : A) (b : B) :
    pairedLabelMean p q (fun omega => pairedCellHit xy a b omega*pairedCellHit uv a b omega) ≤ 1 := by
  have h := finiteExpectation_mono (pairedLabelWeight p q) (pairedLabelWeight_nonneg p q hp hq)
    (Y := fun _ => (1 : ℝ)) (fun omega => by
      simpa only [one_mul] using mul_le_mul (pairedCellHit_le_one xy a b omega)
        (pairedCellHit_le_one uv a b omega) (pairedCellHit_nonneg uv a b omega)
        (by norm_num : (0 : ℝ) ≤ 1))
  exact h.trans_eq (finiteExpectation_const _ (pairedLabelWeight_total p q hpt hqt) 1)

end LatinonEntropy
