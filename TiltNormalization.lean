module

public import PermanentalLaw

@[expose] public section

/-! Row normalization of an exponential tilt. All statements are proved from
the nonnegative unit-row hypothesis, without a permanent upper bound. -/

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

def tiltRowMass (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → Fin n → ℝ)
    (t : ℝ) (i : Fin n) : ℝ := ∑ j, tiltedMatrix Q g t i j

def normalizedTilt (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → Fin n → ℝ)
    (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => tiltedMatrix Q g t i j / tiltRowMass Q g t i

theorem tilt_exponent_bounds (g : Fin n → Fin n → ℝ) (t : ℝ)
    (hg : ∀ i j, |g i j| ≤ 1) (ht : |t| ≤ 1) (i j : Fin n) :
    -1 ≤ t * g i j ∧ t * g i j ≤ 1 := by
  have h : |t * g i j| ≤ 1 := by
    rw [abs_mul]
    have hh := mul_le_mul ht (hg i j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hh
  exact abs_le.mp h

theorem tiltRowMass_bounds (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) (i : Fin n) :
    Real.exp (-1) ≤ tiltRowMass Q g t i ∧ tiltRowMass Q g t i ≤ Real.exp 1 := by
  have hl := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (tilt_exponent_bounds g t hg ht i j).1) (hQ i j))
  have hu := Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) =>
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (tilt_exponent_bounds g t hg ht i j).2) (hQ i j))
  simp only [← Finset.sum_mul, hrow, one_mul] at hl hu
  exact ⟨hl,hu⟩

theorem tiltRowMass_pos (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) (i : Fin n) : 0 < tiltRowMass Q g t i :=
  lt_of_lt_of_le (Real.exp_pos _) (tiltRowMass_bounds Q hQ hrow g hg t ht i).1

theorem normalizedTilt_nonneg (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) (i j : Fin n) : 0 ≤ normalizedTilt Q g t i j :=
  div_nonneg (mul_nonneg (hQ i j) (Real.exp_pos _).le)
    (tiltRowMass_pos Q hQ hrow g hg t ht i).le

theorem normalizedTilt_row (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) (i : Fin n) : (∑ j, normalizedTilt Q g t i j) = 1 := by
  simp only [normalizedTilt, div_eq_mul_inv, ← Finset.sum_mul]
  change tiltRowMass Q g t i * (tiltRowMass Q g t i)⁻¹ = 1
  exact mul_inv_cancel₀ (tiltRowMass_pos Q hQ hrow g hg t ht i).ne'

theorem normalizedTilt_entry_le (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) (i j : Fin n) :
    normalizedTilt Q g t i j ≤ Real.exp 2 * Q i j := by
  have hp := tiltRowMass_pos Q hQ hrow g hg t ht i
  have hl := (tiltRowMass_bounds Q hQ hrow g hg t ht i).1
  have hu := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (tilt_exponent_bounds g t hg ht i j).2) (hQ i j)
  have he : Real.exp 2 * Real.exp (-1) = Real.exp 1 := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  have hm := mul_le_mul_of_nonneg_left hl
    (mul_nonneg (Real.exp_pos 2).le (hQ i j))
  have hid : (Real.exp 2 * Q i j) * Real.exp (-1) = Q i j * Real.exp 1 := by
    calc
      _ = Q i j * (Real.exp 2 * Real.exp (-1)) := by ring
      _ = _ := by rw [he]
  rw [hid] at hm
  apply (div_le_iff₀ hp).mpr
  exact hu.trans hm

theorem tilted_permanent_normalized (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (g : Fin n → Fin n → ℝ) (hg : ∀ i j, |g i j| ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1) :
    (tiltedMatrix Q g t).permanent =
      (∏ i, tiltRowMass Q g t i) * (normalizedTilt Q g t).permanent := by
  have heq : tiltedMatrix Q g t =
      (fun i j => tiltRowMass Q g t i * normalizedTilt Q g t i j) := by
    funext i j
    have hp := (tiltRowMass_pos Q hQ hrow g hg t ht i).ne'
    simp [normalizedTilt,div_eq_mul_inv,mul_comm,hp]
  calc
    (tiltedMatrix Q g t).permanent =
        Matrix.permanent (fun i j => tiltRowMass Q g t i * normalizedTilt Q g t i j) :=
      congrArg Matrix.permanent heq
    _ = _ := permanent_row_scale _ _

end LatinonEntropy

#print axioms LatinonEntropy.normalizedTilt_entry_le
#print axioms LatinonEntropy.tilted_permanent_normalized
