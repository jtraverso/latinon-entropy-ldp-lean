module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Matrix Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixAssignmentCost (c : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun M := ∑ i, ∑ j, M i j*c i j
  map_add' A B := by simp [add_mul,sum_add_distrib]
  map_smul' a A := by simp [mul_assoc,mul_sum]

/-- The assignment step needed to approximate the actual order map:
a permutation costs no more than any doubly stochastic transport. -/
theorem exists_permutation_cost_le_fractional (P c : Matrix ι ι ℝ)
    (hP : P ∈ doublyStochastic ℝ ι) :
    ∃ sigma : Equiv.Perm ι, (∑ i, c i (sigma i)) ≤ ∑ i, ∑ j, P i j*c i j := by
  have hh : P ∈ convexHull ℝ {sigma.permMatrix ℝ | sigma : Equiv.Perm ι} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]
    exact hP
  obtain ⟨_,⟨sigma,rfl⟩,hs⟩ :=
    ((matrixAssignmentCost c).concaveOn convex_univ).exists_le_of_mem_convexHull (by simp) hh
  refine ⟨sigma,?_⟩
  simpa [matrixAssignmentCost,Equiv.toPEquiv_apply] using hs

end LatinonEntropy

#print axioms LatinonEntropy.matrixAssignmentCost
#print axioms LatinonEntropy.exists_permutation_cost_le_fractional
