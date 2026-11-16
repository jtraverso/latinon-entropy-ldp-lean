module

public import FiniteLabelProducts

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem productLabelMean_apply_mul {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i j : I) (hij : i ≠ j)
    (g h : A → ℝ) :
    productLabelMean p (fun ell => g (ell i)*h (ell j)) =
      (∑ a, p i a*g a)*(∑ a, p j a*h a) := by
  have hji : j ≠ i := Ne.symm hij
  calc
    _ = productLabelMean p (fun ell => ∏ k : I,
        (if k = i then g (ell k) else 1)*(if k = j then h (ell k) else 1)) := by
      apply finiteExpectation_congr
      intro ell
      rw [prod_mul_distrib]
      simp
    _ = ∏ k : I, ∑ a, p k a*((if k = i then g a else 1)*(if k = j then h a else 1)) :=
      productLabelMean_prod p (fun k a => (if k = i then g a else 1)*(if k = j then h a else 1))
    _ = ∏ k : I, (if k = i then (∑ a, p i a*g a) else 1)*
        (if k = j then (∑ a, p j a*h a) else 1) := by
      apply prod_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp only [ite_true,hij,ite_false,mul_one]
      · by_cases hkj : k = j
        · subst k
          simp only [hji,ite_false,ite_true,one_mul]
        · simp only [hki,hkj,ite_false,mul_one,hp]
    _ = _ := by rw [prod_mul_distrib]; simp

def labelHit {I A : Type*} (i : I) (a : A) (ell : I → A) : ℝ :=
  if ell i = a then 1 else 0

theorem labelHit_nonneg {I A : Type*} (i : I) (a : A) (ell : I → A) :
    0 ≤ labelHit i a ell := by unfold labelHit; split_ifs <;> norm_num

theorem labelHit_le_one {I A : Type*} (i : I) (a : A) (ell : I → A) :
    labelHit i a ell ≤ 1 := by unfold labelHit; split_ifs <;> norm_num

theorem labelHit_mul_self {I A : Type*} (i : I) (a : A) (ell : I → A) :
    labelHit i a ell*labelHit i a ell = labelHit i a ell := by
  unfold labelHit
  split_ifs <;> norm_num

theorem productLabelMean_hit {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i : I) (a : A) :
    productLabelMean p (labelHit i a) = p i a := by
  have h := productLabelMean_apply p hp i (fun b => if b = a then (1 : ℝ) else 0)
  calc
    _ = productLabelMean p (fun ell => if ell i = a then (1 : ℝ) else 0) := by
      apply finiteExpectation_congr
      intro ell
      by_cases he : ell i = a
      · simp only [labelHit,he,ite_true]
      · simp only [labelHit,he,ite_false]
    _ = _ := by simpa using h

theorem productLabelMean_hit_pair {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i j : I) (a : A) :
    productLabelMean p (fun ell => labelHit i a ell*labelHit j a ell) =
      if i = j then p i a else p i a*p j a := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    calc
      _ = productLabelMean p (labelHit i a) :=
        finiteExpectation_congr _ (labelHit_mul_self i a)
      _ = _ := productLabelMean_hit p hp i a
  · simp only [hij,ite_false]
    have h := productLabelMean_apply_mul p hp i j hij
      (fun b => if b = a then (1 : ℝ) else 0) (fun b => if b = a then (1 : ℝ) else 0)
    simpa [labelHit] using h

theorem productLabelMean_hit_pair_le_one {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (htotal : ∀ i, ∑ a, p i a = 1)
    (i j : I) (a : A) :
    productLabelMean p (fun ell => labelHit i a ell*labelHit j a ell) ≤ 1 := by
  rw [productLabelMean_hit_pair p htotal]
  split_ifs
  · exact label_probability_le_one p hp htotal i a
  · simpa only [one_mul] using mul_le_mul (label_probability_le_one p hp htotal i a)
      (label_probability_le_one p hp htotal j a) (hp j a) (by norm_num : (0 : ℝ) ≤ 1)

end LatinonEntropy
