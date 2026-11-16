module

public import ResidualPotential

@[expose] public section

/-! Existence of the bounded transportation L1 optimizer.
The box may encode forbidden edges by setting both endpoint functions to zero.
Feasibility is supplied by a witness; in the paper this witness is A/d. -/

noncomputable section

namespace LatinonEntropy

theorem exists_box_correction_minimizer
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (M lower upper Q0 : Y → Z → ℝ)
    (hbox0 : Q0 ∈ Set.Icc lower upper)
    (hrow0 : ∀ y, ∑ z, Q0 y z = 1)
    (hcol0 : ∀ z, ∑ y, Q0 y z = 1) :
    ∃ Q : Y → Z → ℝ, Q ∈ Set.Icc lower upper ∧
      (∀ y, ∑ z, Q y z = 1) ∧ (∀ z, ∑ y, Q y z = 1) ∧
      ∀ P : Y → Z → ℝ, P ∈ Set.Icc lower upper →
        (∀ y, ∑ z, P y z = 1) → (∀ z, ∑ y, P y z = 1) →
        (∑ y, ∑ z, |Q y z - M y z|) ≤ ∑ y, ∑ z, |P y z - M y z| := by
  let rows : Set (Y → Z → ℝ) := {Q | (fun y => ∑ z, Q y z) = fun _ => 1}
  let cols : Set (Y → Z → ℝ) := {Q | (fun z => ∑ y, Q y z) = fun _ => 1}
  have hrows : IsClosed rows := isClosed_eq (by fun_prop) continuous_const
  have hcols : IsClosed cols := isClosed_eq (by fun_prop) continuous_const
  let F := Set.Icc lower upper ∩ (rows ∩ cols)
  have hcompact : IsCompact F := isCompact_Icc.inter_right (hrows.inter hcols)
  have hne : F.Nonempty := ⟨Q0, hbox0, funext hrow0, funext hcol0⟩
  have hcost : Continuous (fun Q : Y → Z → ℝ => ∑ y, ∑ z, |Q y z - M y z|) := by
    fun_prop
  obtain ⟨Q, hQ, hmin⟩ := hcompact.exists_isMinOn hne hcost.continuousOn
  refine ⟨Q, hQ.1, fun y => congrFun hQ.2.1 y, fun z => congrFun hQ.2.2 z, ?_⟩
  intro P hbox hrow hcol
  exact hmin ⟨hbox, funext hrow, funext hcol⟩

end LatinonEntropy

#print axioms LatinonEntropy.exists_box_correction_minimizer
