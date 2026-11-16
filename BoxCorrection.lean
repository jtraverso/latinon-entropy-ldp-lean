module

public import ResidualWalks

@[expose] public section

/-! The analytic/optimization part of the correction theorem is assembled.
The remaining graph-specific hypothesis is the residual diameter bound for
every feasible matrix. The quasirandom-cut implication is a separate lemma. -/

noncomputable section

namespace LatinonEntropy

theorem exists_box_correction_of_residual_diameter
    {Y Z : Type*} [Fintype Y] [Fintype Z] [Nonempty Y] [Nonempty Z]
    (M lower upper Q0 : Y → Z → ℝ)
    (hM : M ∈ Set.Icc lower upper)
    (hbox0 : Q0 ∈ Set.Icc lower upper)
    (hrow0 : ∀ y, ∑ z, Q0 y z = 1) (hcol0 : ∀ z, ∑ y, Q0 y z = 1)
    (hdiam : ∀ Q : Y → Z → ℝ, Q ∈ Set.Icc lower upper →
      (∀ y, ∑ z, Q y z = 1) → (∀ z, ∑ y, Q y z = 1) →
      ∀ u v, ∃ t n,
        CostWalk (boxResidual lower upper Q) (boxResidualCost M Q) u v t n ∧ n ≤ 6) :
    ∃ Q : Y → Z → ℝ, Q ∈ Set.Icc lower upper ∧
      (∀ y, ∑ z, Q y z = 1) ∧ (∀ z, ∑ y, Q y z = 1) ∧
      (∑ y, ∑ z, |Q y z - M y z|) ≤
        3 * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  obtain ⟨Q, hbox, hrow, hcol, hmin⟩ :=
    exists_box_correction_minimizer M lower upper Q0 hbox0 hrow0 hcol0
  refine ⟨Q, hbox, hrow, hcol, ?_⟩
  apply correction_cost_of_residual_graph M Q
    (boxResidual lower upper Q) (boxResidualCost M Q) hrow hcol
    (fun u v _ => boxResidualCost_le_one M Q u v) (hdiam Q hbox hrow hcol)
    (residual_closed_walk_nonnegative M lower upper Q hbox hrow hcol hmin)
  · intro y z h
    refine ⟨lt_of_lt_of_le h (hM.2 y z), ?_⟩
    simp [boxResidualCost, forwardCost, h]
  · intro y z h
    refine ⟨lt_of_le_of_lt (hM.1 y z) h, ?_⟩
    simp [boxResidualCost, backwardCost, h]

end LatinonEntropy

#print axioms LatinonEntropy.exists_box_correction_of_residual_diameter
