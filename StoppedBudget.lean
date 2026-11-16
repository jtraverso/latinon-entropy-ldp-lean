module

public import HistoryMartingale
public import StoppedAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

def historyPastLive {Ω : Type*} (Good : List Ω → Prop) : List Ω → Prop
  | [] => True
  | _a::h => historyLive Good h

theorem historyLive_pastLive {Ω : Type*} (Good : List Ω → Prop) (h : List Ω)
    (hlive : historyLive Good h) : historyPastLive Good h := by
  cases h with
  | nil => trivial
  | cons a h => exact hlive.1

theorem historyLive_iff_good_of_past {Ω : Type*} (Good : List Ω → Prop) (h : List Ω)
    (hpast : historyPastLive Good h) : historyLive Good h ↔ Good h := by
  cases h with
  | nil => rfl
  | cons a h => exact and_iff_right hpast

theorem stopped_budget_eq_of_past {Ω : Type*} (Good : List Ω → Prop) (cost : List Ω → ℝ)
    (h : List Ω) (hpast : historyPastLive Good h) :
    pathSum (fun g (_ : Ω) => if historyLive Good g then cost g else 0) h =
      pathSum (fun g (_ : Ω) => cost g) h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    have hlive : historyLive Good h := hpast
    simp only [pathSum,hlive,ite_true,ih (historyLive_pastLive Good h hlive)]

def budgetedGood {Ω : Type*} (Guard : List Ω → Prop) (cost : List Ω → ℝ)
    (budget : ℝ) (h : List Ω) : Prop :=
  Guard h ∧ pathSum (fun g (_ : Ω) => cost g) h ≤ budget

/-- A first failure is either a local guard failure or an exceeded stopped
budget. No cost incurred after stopping enters the second alternative. -/
theorem budgeted_first_failure {Ω : Type*} (Guard : List Ω → Prop) (cost : List Ω → ℝ)
    (budget : ℝ) (h : List Ω)
    (hpast : historyPastLive (budgetedGood Guard cost budget) h)
    (hstop : ¬historyLive (budgetedGood Guard cost budget) h) :
    ¬Guard h ∨ budget < pathSum (fun g (_ : Ω) =>
      if historyLive (budgetedGood Guard cost budget) g then cost g else 0) h := by
  by_cases hg : Guard h
  · right
    have hng : ¬budgetedGood Guard cost budget h := fun hh =>
      hstop ((historyLive_iff_good_of_past _ h hpast).mpr hh)
    have hnot : ¬pathSum (fun g (_ : Ω) => cost g) h ≤ budget := fun hb => hng ⟨hg,hb⟩
    rw [stopped_budget_eq_of_past _ cost h hpast]
    exact lt_of_not_ge hnot
  · exact Or.inl hg

end LatinonEntropy

#print axioms LatinonEntropy.stopped_budget_eq_of_past
#print axioms LatinonEntropy.budgeted_first_failure
