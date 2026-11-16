module

public import FiniteWeightedExpectation
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def productLabelWeight {I A : Type*} [Fintype I]
    (p : I → A → ℝ) (ell : I → A) : ℝ := ∏ i, p i (ell i)

def productLabelMean {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (X : (I → A) → ℝ) : ℝ :=
  finiteExpectation (productLabelWeight p) X

theorem productLabelWeight_nonneg {I A : Type*} [Fintype I]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (ell : I → A) :
    0 ≤ productLabelWeight p ell := prod_nonneg (fun i _ => hp i (ell i))

theorem productLabelWeight_total {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ ell : I → A, productLabelWeight p ell) = 1 := by
  unfold productLabelWeight
  rw [← Fintype.prod_sum]
  simp only [hp,prod_const_one]

theorem productLabelMean_const {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (c : ℝ) :
    productLabelMean p (fun _ => c) = c :=
  finiteExpectation_const _ (productLabelWeight_total p hp) c

theorem productLabelMean_prod {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p g : I → A → ℝ) :
    productLabelMean p (fun ell => ∏ i, g i (ell i)) = ∏ i, ∑ a, p i a*g i a := by
  unfold productLabelMean finiteExpectation productLabelWeight
  simp only [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => p i a*g i a)).symm

theorem productLabelMean_apply {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i : I) (g : A → ℝ) :
    productLabelMean p (fun ell => g (ell i)) = ∑ a, p i a*g a := by
  calc
    _ = productLabelMean p (fun ell => ∏ j : I, if j = i then g (ell j) else 1) := by
      apply finiteExpectation_congr
      intro ell
      simp
    _ = ∏ j : I, ∑ a, p j a*(if j = i then g a else 1) :=
      productLabelMean_prod p (fun j a => if j = i then g a else 1)
    _ = ∏ j : I, if j = i then (∑ a, p i a*g a) else 1 := by
      apply prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [ite_true]
      · simp only [hji,ite_false,mul_one,hp]
    _ = _ := by simp

theorem label_probability_le_one {I A : Type*} [Fintype A]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (htotal : ∀ i, ∑ a, p i a = 1)
    (i : I) (a : A) : p i a ≤ 1 := by
  have h := single_le_sum (f := p i) (fun b _ => hp i b) (mem_univ a)
  rw [htotal i] at h
  exact h

end LatinonEntropy
