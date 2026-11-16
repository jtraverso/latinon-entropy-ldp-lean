module

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical

theorem integrable_unit_weight {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (K f : X → ℝ) (hK : Integrable K mu) (hf : Measurable f)
    (hfb : ∀ᵐ x ∂mu, f x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x => f x*K x) mu := by
  apply hK.bdd_mul hf.aestronglyMeasurable
  filter_upwards [hfb] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg hx.1]
  exact hx.2

/-- Multiplication by a measurable weight in [0,1] cannot exceed the
integral on the positive region of a signed integrable function. -/
theorem integral_unit_weight_le_of_set_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (K f : X → ℝ) (hKm : Measurable K) (hK : Integrable K mu)
    (hf : Measurable f) (hfb : ∀ᵐ x ∂mu, f x ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (hset : ∀ S : Set X, MeasurableSet S → (∫ x in S, K x ∂mu) ≤ eps) :
    (∫ x, f x*K x ∂mu) ≤ eps := by
  let P : Set X := {x | 0 ≤ K x}
  have hP : MeasurableSet P := measurableSet_le measurable_const hKm
  have hdom : ∀ᵐ x ∂mu, f x*K x ≤ P.indicator K x := by
    filter_upwards [hfb] with x hx
    by_cases hp : 0 ≤ K x
    · rw [Set.indicator_of_mem (show x ∈ P from hp)]
      exact mul_le_of_le_one_left hp hx.2
    · rw [Set.indicator_of_notMem (show x ∉ P from hp)]
      exact mul_nonpos_of_nonneg_of_nonpos hx.1 (le_of_not_ge hp)
  calc
    (∫ x, f x*K x ∂mu) ≤ ∫ x, P.indicator K x ∂mu :=
      integral_mono_ae (integrable_unit_weight mu K f hK hf hfb) (hK.indicator hP) hdom
    _ = ∫ x in P, K x ∂mu := integral_indicator hP
    _ ≤ eps := hset P hP

/-- The signed one-variable weighted bound has the same constant as the
bound for all measurable sets. Bounds on the weight are only almost everywhere. -/
theorem abs_integral_unit_weight_le_of_set_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (K f : X → ℝ) (hKm : Measurable K) (hK : Integrable K mu)
    (hf : Measurable f) (hfb : ∀ᵐ x ∂mu, f x ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (hset : ∀ S : Set X, MeasurableSet S → |∫ x in S, K x ∂mu| ≤ eps) :
    |∫ x, f x*K x ∂mu| ≤ eps := by
  have hupper := integral_unit_weight_le_of_set_bound mu K f hKm hK hf hfb eps
    (fun S hS => (le_abs_self _).trans (hset S hS))
  have hneg : ∀ S : Set X, MeasurableSet S → (∫ x in S, -K x ∂mu) ≤ eps := by
    intro S hS
    rw [integral_neg]
    exact (neg_le_abs _).trans (hset S hS)
  have hlower := integral_unit_weight_le_of_set_bound mu (fun x => -K x) f hKm.neg hK.neg hf hfb eps hneg
  simp only [mul_neg,integral_neg] at hlower
  exact abs_le.mpr ⟨by linarith only [hlower],hupper⟩

end LatinonEntropy

#print axioms LatinonEntropy.integrable_unit_weight
#print axioms LatinonEntropy.integral_unit_weight_le_of_set_bound
#print axioms LatinonEntropy.abs_integral_unit_weight_le_of_set_bound
