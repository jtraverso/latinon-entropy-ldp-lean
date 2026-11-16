module

public import FiniteWeightedExpectation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def finiteCovariance {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) : ℝ :=
  finiteExpectation w (fun omega => X omega*Y omega)-finiteExpectation w X*finiteExpectation w Y

def finiteVariance {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) : ℝ :=
  finiteExpectation w (fun omega => (X omega-finiteExpectation w X)^2)

theorem finiteExpectation_div {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun omega => X omega/c) = finiteExpectation w X/c := by
  unfold finiteExpectation
  simp only [← mul_div_assoc,← sum_div]

theorem finiteVariance_nonneg {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (hw : ∀ omega, 0 ≤ w omega) : 0 ≤ finiteVariance w X :=
  finiteExpectation_nonneg w _ hw (fun _ => sq_nonneg _)

theorem finiteVariance_eq_second_moment {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (htotal : ∑ omega, w omega = 1) :
    finiteVariance w X = finiteExpectation w (fun omega => X omega^2)-(finiteExpectation w X)^2 := by
  unfold finiteVariance
  calc
    _ = finiteExpectation w (fun omega => X omega^2-2*finiteExpectation w X*X omega+
        (finiteExpectation w X)^2) := finiteExpectation_congr w (fun omega => by ring)
    _ = finiteExpectation w (fun omega => X omega^2)-2*finiteExpectation w X*finiteExpectation w X+
        (finiteExpectation w X)^2 := by
      rw [finiteExpectation_add,finiteExpectation_sub,finiteExpectation_mul_left,
        finiteExpectation_const w htotal]
    _ = _ := by ring

/-- Expansion of the variance under the actual normalized finite weights.
No independence or covariance hypothesis is inserted. -/
theorem finiteVariance_sum {Ω I : Type*} [Fintype Ω]
    (w : Ω → ℝ) (htotal : ∑ omega, w omega = 1) (S : Finset I)
    (C : I → ℝ) (X : I → Ω → ℝ) :
    finiteVariance w (fun omega => ∑ i ∈ S, C i*X i omega) =
      ∑ i ∈ S, ∑ j ∈ S, C i*C j*finiteCovariance w (X i) (X j) := by
  have hE : finiteExpectation w (fun omega => (∑ i ∈ S, C i*X i omega)^2) =
      ∑ i ∈ S, ∑ j ∈ S, C i*C j*finiteExpectation w (fun omega => X i omega*X j omega) := by
    calc
      _ = finiteExpectation w (fun omega => ∑ i ∈ S, ∑ j ∈ S, C i*C j*(X i omega*X j omega)) := by
        apply finiteExpectation_congr
        intro omega
        rw [pow_two,sum_mul]
        simp only [mul_sum]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by simp_rw [finiteExpectation_sum,finiteExpectation_mul_left]
  have hmean : finiteExpectation w (fun omega => ∑ i ∈ S, C i*X i omega) =
      ∑ i ∈ S, C i*finiteExpectation w (X i) := by
    simp_rw [finiteExpectation_sum,finiteExpectation_mul_left]
  rw [finiteVariance_eq_second_moment w _ htotal,hE,hmean]
  simp only [finiteCovariance,mul_sub,sum_sub_distrib]
  congr 1
  rw [pow_two,sum_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

end LatinonEntropy
