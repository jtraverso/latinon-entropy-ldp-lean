module

public import FiniteCore
public import Mathlib.LinearAlgebra.Matrix.Permanent

@[expose] public section

/-! Exact finite identities for the permanental distribution. Mathlib indexes
the permanent by columns; `permWeight` uses the row convention of the Latin
process. The equality between the two conventions is proved by transposition.
No permanent upper or lower bound is assumed or asserted in this file. -/

noncomputable section

namespace LatinonEntropy

open Finset

variable {n : ℕ}

def permWeight (Q : Matrix (Fin n) (Fin n) ℝ) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i, Q i (sigma i)

theorem sum_permWeight (Q : Matrix (Fin n) (Fin n) ℝ) :
    (∑ sigma, permWeight Q sigma) = Q.permanent := by
  rw [← Matrix.permanent_transpose Q]
  rfl

def permanentLaw (Q : Matrix (Fin n) (Fin n) ℝ) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  permWeight Q sigma / Q.permanent

def permanentMarginal (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ sigma, if sigma i = j then permanentLaw Q sigma else 0

def permutationStatistic (g : Fin n → Fin n → ℝ) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, g i (sigma i)

theorem permWeight_nonneg (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (sigma : Equiv.Perm (Fin n)) : 0 ≤ permWeight Q sigma :=
  Finset.prod_nonneg fun i _ => hQ i (sigma i)

theorem permanent_nonneg (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    0 ≤ Q.permanent := by
  rw [← sum_permWeight]
  exact Finset.sum_nonneg fun sigma _ => permWeight_nonneg Q hQ sigma

theorem permanentLaw_nonneg (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent) (sigma : Equiv.Perm (Fin n)) :
    0 ≤ permanentLaw Q sigma := div_nonneg (permWeight_nonneg Q hQ sigma) hper.le

theorem sum_permanentLaw (Q : Matrix (Fin n) (Fin n) ℝ) (hper : Q.permanent ≠ 0) :
    (∑ sigma, permanentLaw Q sigma) = 1 := by
  simp only [permanentLaw, div_eq_mul_inv, ← Finset.sum_mul, sum_permWeight]
  exact mul_inv_cancel₀ hper

theorem permanentMarginal_nonneg (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent) (i j : Fin n) :
    0 ≤ permanentMarginal Q i j := by
  apply Finset.sum_nonneg
  intro sigma _
  split_ifs
  · exact permanentLaw_nonneg Q hQ hper sigma
  · exact le_rfl

theorem permanentMarginal_row (Q : Matrix (Fin n) (Fin n) ℝ)
    (hper : Q.permanent ≠ 0) (i : Fin n) : (∑ j, permanentMarginal Q i j) = 1 := by
  classical
  unfold permanentMarginal
  rw [Finset.sum_comm]
  simpa using sum_permanentLaw Q hper

theorem permanentMarginal_col (Q : Matrix (Fin n) (Fin n) ℝ)
    (hper : Q.permanent ≠ 0) (j : Fin n) : (∑ i, permanentMarginal Q i j) = 1 := by
  classical
  unfold permanentMarginal
  rw [Finset.sum_comm]
  have hinner : ∀ sigma : Equiv.Perm (Fin n),
      (∑ i, if sigma i = j then permanentLaw Q sigma else 0) = permanentLaw Q sigma := by
    intro sigma
    have hi : ∀ i, sigma i = j ↔ i = sigma.symm j := by
      intro i
      constructor
      · intro h
        simpa using congrArg sigma.symm h
      · intro h
        subst i
        simp
    simp_rw [hi]
    simp
  simp only [hinner]
  exact sum_permanentLaw Q hper

theorem permanentMarginal_pairing (Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, permanentMarginal Q i j * g i j) =
      ∑ sigma, permanentLaw Q sigma * permutationStatistic g sigma := by
  classical
  have hrow : ∀ i, (∑ j, permanentMarginal Q i j * g i j) =
      ∑ sigma, permanentLaw Q sigma * g i (sigma i) := by
    intro i
    unfold permanentMarginal
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sigma _
    simp only [ite_mul, zero_mul]
    simp
  simp_rw [hrow]
  rw [Finset.sum_comm]
  simp only [permutationStatistic, Finset.mul_sum]

def tiltedMatrix (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Q i j * Real.exp (t * g i j)

theorem tilted_permWeight (Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) (t : ℝ) (sigma : Equiv.Perm (Fin n)) :
    permWeight (tiltedMatrix Q g t) sigma =
      permWeight Q sigma * Real.exp (t * permutationStatistic g sigma) := by
  unfold permWeight tiltedMatrix permutationStatistic
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]

/-- The exact MGF identity; positivity is needed to interpret the weights as
a probability law, but not for this algebraic equality. -/
theorem permanentLaw_mgf (Q : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → Fin n → ℝ) (t : ℝ) :
    (∑ sigma, permanentLaw Q sigma * Real.exp (t * permutationStatistic g sigma)) =
      (tiltedMatrix Q g t).permanent / Q.permanent := by
  calc
    (∑ sigma, permanentLaw Q sigma * Real.exp (t * permutationStatistic g sigma)) =
        ∑ sigma, permWeight (tiltedMatrix Q g t) sigma / Q.permanent := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [tilted_permWeight]
      unfold permanentLaw
      ring
    _ = (∑ sigma, permWeight (tiltedMatrix Q g t) sigma) / Q.permanent := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = (tiltedMatrix Q g t).permanent / Q.permanent := by rw [sum_permWeight]

theorem permanent_row_scale (Q : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) :
    Matrix.permanent (fun i j => r i * Q i j) =
      (∏ i, r i) * Q.permanent := by
  let P : Matrix (Fin n) (Fin n) ℝ := fun i j => r i * Q i j
  change P.permanent = (∏ i, r i) * Q.permanent
  rw [← sum_permWeight P, ← sum_permWeight Q]
  simp only [permWeight, P, Finset.prod_mul_distrib, Finset.mul_sum]

theorem exists_positive_permWeight (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent) :
    ∃ sigma, 0 < permWeight Q sigma := by
  by_contra! h
  have hz : ∀ sigma, permWeight Q sigma = 0 :=
    fun sigma => le_antisymm (h sigma) (permWeight_nonneg Q hQ sigma)
  have hp : Q.permanent = 0 := by rw [← sum_permWeight]; simp [hz]
  linarith

theorem tilted_permanent_pos (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hper : 0 < Q.permanent)
    (g : Fin n → Fin n → ℝ) (t : ℝ) : 0 < (tiltedMatrix Q g t).permanent := by
  obtain ⟨sigma, hs⟩ := exists_positive_permWeight Q hQ hper
  have ht : 0 < permWeight (tiltedMatrix Q g t) sigma := by
    rw [tilted_permWeight]
    exact mul_pos hs (Real.exp_pos _)
  have hn : ∀ tau, 0 ≤ permWeight (tiltedMatrix Q g t) tau := by
    intro tau
    rw [tilted_permWeight]
    exact mul_nonneg (permWeight_nonneg Q hQ tau) (Real.exp_pos _).le
  rw [← sum_permWeight]
  exact lt_of_lt_of_le ht (Finset.single_le_sum (fun tau _ => hn tau) (mem_univ sigma))

end LatinonEntropy

#print axioms LatinonEntropy.permanentMarginal_pairing
#print axioms LatinonEntropy.permanentLaw_mgf
#print axioms LatinonEntropy.tilted_permanent_pos
