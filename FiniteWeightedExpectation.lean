module

public import FiniteAverages

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def finiteExpectation {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ omega, w omega*X omega

theorem finiteExpectation_congr {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    {X Y : Ω → ℝ} (h : ∀ omega, X omega = Y omega) :
    finiteExpectation w X = finiteExpectation w Y := by
  unfold finiteExpectation
  exact sum_congr rfl (fun omega _ => congrArg (fun t => w omega*t) (h omega))

theorem finiteExpectation_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∑ omega, w omega = 1) (c : ℝ) : finiteExpectation w (fun _ => c) = c := by
  rw [finiteExpectation,← sum_mul,hw,one_mul]

theorem finiteExpectation_add {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) :
    finiteExpectation w (fun omega => X omega+Y omega) =
      finiteExpectation w X+finiteExpectation w Y := by
  simp only [finiteExpectation,mul_add,sum_add_distrib]

theorem finiteExpectation_sub {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) :
    finiteExpectation w (fun omega => X omega-Y omega) =
      finiteExpectation w X-finiteExpectation w Y := by
  simp only [finiteExpectation,mul_sub,sum_sub_distrib]

theorem finiteExpectation_mul_left {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun omega => c*X omega) = c*finiteExpectation w X := by
  unfold finiteExpectation
  rw [mul_sum]
  apply sum_congr rfl
  intro omega _
  ring

theorem finiteExpectation_mul_right {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun omega => X omega*c) = finiteExpectation w X*c := by
  unfold finiteExpectation
  simp only [← mul_assoc,← sum_mul]

theorem finiteExpectation_sum {Ω I : Type*} [Fintype Ω]
    (w : Ω → ℝ) (S : Finset I) (X : I → Ω → ℝ) :
    finiteExpectation w (fun omega => ∑ i ∈ S, X i omega) =
      ∑ i ∈ S, finiteExpectation w (X i) := by
  unfold finiteExpectation
  simp only [mul_sum]
  rw [sum_comm]

theorem finiteExpectation_nonneg {Ω : Type*} [Fintype Ω]
    (w X : Ω → ℝ) (hw : ∀ omega, 0 ≤ w omega) (hX : ∀ omega, 0 ≤ X omega) :
    0 ≤ finiteExpectation w X := sum_nonneg (fun omega _ => mul_nonneg (hw omega) (hX omega))

theorem finiteExpectation_mono {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ omega, 0 ≤ w omega) {X Y : Ω → ℝ}
    (hXY : ∀ omega, X omega ≤ Y omega) :
    finiteExpectation w X ≤ finiteExpectation w Y :=
  sum_le_sum (fun omega _ => mul_le_mul_of_nonneg_left (hXY omega) (hw omega))

/-- A normalized finite law whose mean is below t has a positive-weight
outcome below t. This constructs the good rounding outcome from its cost. -/
theorem finiteExpectation_exists_lt {Ω : Type*} [Fintype Ω]
    (w X : Ω → ℝ) (hw : ∀ omega, 0 ≤ w omega) (htotal : ∑ omega, w omega = 1)
    (t : ℝ) (hmean : finiteExpectation w X < t) :
    ∃ omega, 0 < w omega ∧ X omega < t := by
  by_contra! hbad
  have hp : ∀ omega, w omega*t ≤ w omega*X omega := by
    intro omega
    by_cases hz : w omega = 0
    · simp only [hz,zero_mul,le_refl]
    · have hwpos : 0 < w omega := lt_of_le_of_ne (hw omega) (Ne.symm hz)
      exact mul_le_mul_of_nonneg_left (hbad omega hwpos) (hw omega)
  have hs := sum_le_sum (fun omega (_ : omega ∈ (univ : Finset Ω)) => hp omega)
  rw [← sum_mul,htotal,one_mul] at hs
  exact (not_le_of_gt hmean) hs

end LatinonEntropy
