module

public import MeasurableAlignmentWeights
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical

theorem finite_indicator_setIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {r : ℕ}
    (S : Set α) (E : Fin r → Set α) (hE : ∀ i, MeasurableSet (E i)) (c : Fin r → ℝ) :
    (∫ x in S, ∑ i, (E i).indicator (fun _ => c i) x ∂μ) =
      ∑ i, μ.real (S ∩ E i)*c i := by
  rw [integral_finsetSum univ (fun i _ => (integrable_const (c i)).indicator (hE i))]
  apply sum_congr rfl
  intro i _
  rw [setIntegral_indicator (hE i),setIntegral_const,smul_eq_mul]

def finiteRectangleStep {α : Type*} {r s : ℕ}
    (E : Fin r → Set α) (F : Fin s → Set α) (c : Fin r → Fin s → ℝ)
    (u v : α) : ℝ :=
  ∑ i, (E i).indicator (fun _ => ∑ j, (F j).indicator (fun _ => c i j) v) u

theorem finiteRectangleStep_inner_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {r s : ℕ}
    (T : Set α) (E : Fin r → Set α) (F : Fin s → Set α)
    (hF : ∀ j, MeasurableSet (F j)) (c : Fin r → Fin s → ℝ) (u : α) :
    (∫ v in T, finiteRectangleStep E F c u v ∂μ) =
      ∑ i, (E i).indicator (fun _ => ∑ j, μ.real (T ∩ F j)*c i j) u := by
  have hi : ∀ i, Integrable
      (fun v => (E i).indicator (fun _ => ∑ j, (F j).indicator (fun _ => c i j) v) u)
      (μ.restrict T) := by
    intro i
    by_cases hu : u ∈ E i
    · simpa only [Set.indicator_of_mem hu] using
        (integrable_finsetSum univ (fun j _ => (integrable_const (c i j)).indicator (hF j)))
    · simpa only [Set.indicator_of_notMem hu] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : α => (0 : ℝ)) (μ.restrict T))
  unfold finiteRectangleStep
  rw [integral_finsetSum univ (fun i _ => hi i)]
  apply sum_congr rfl
  intro i _
  by_cases hu : u ∈ E i
  · simp only [Set.indicator_of_mem hu]
    exact finite_indicator_setIntegral μ T F hF (c i)
  · simp only [Set.indicator_of_notMem hu,integral_zero]

/-- Exact iterated cut integral of a finite rectangle step function. -/
theorem finiteRectangleStep_rectangle_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {r s : ℕ}
    (S T : Set α) (E : Fin r → Set α) (F : Fin s → Set α)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ j, MeasurableSet (F j))
    (c : Fin r → Fin s → ℝ) :
    (∫ u in S, ∫ v in T, finiteRectangleStep E F c u v ∂μ ∂μ) =
      ∑ i, ∑ j, μ.real (S ∩ E i)*μ.real (T ∩ F j)*c i j := by
  simp_rw [finiteRectangleStep_inner_integral μ T E F hF c]
  rw [finite_indicator_setIntegral μ S E hE]
  simp only [mul_sum,mul_assoc]

end LatinonEntropy

#print axioms LatinonEntropy.finite_indicator_setIntegral
#print axioms LatinonEntropy.finiteRectangleStep_inner_integral
#print axioms LatinonEntropy.finiteRectangleStep_rectangle_integral
