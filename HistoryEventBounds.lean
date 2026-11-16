module

public import ProfileSurvivalProbability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def historyEventMass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (N : ℕ) (E : List Ω → Prop) : ℝ :=
  ∑ h ∈ histories Ω N, @ite ℝ (E h) (Classical.propDecidable (E h)) (historyWeight K h) 0

theorem history_event_mass_split {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (N : ℕ) (E A B : List Ω → Prop)
    (hsplit : ∀ h ∈ histories Ω N, 0 < historyWeight K h → E h → A h ∨ B h) :
    historyEventMass K N E ≤ historyEventMass K N A+historyEventMass K N B := by
  simpa only [historyEventMass,history_event_indicator_canonical] using history_event_split K N E A B hsplit

theorem history_event_mass_three_split {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (N : ℕ) (E A B C : List Ω → Prop)
    (hsplit : ∀ h ∈ histories Ω N, 0 < historyWeight K h → E h → A h ∨ B h ∨ C h) :
    historyEventMass K N E ≤ historyEventMass K N A+historyEventMass K N B+historyEventMass K N C := by
  have h1 := history_event_mass_split K N E A (fun h => B h ∨ C h) hsplit
  have h2 := history_event_mass_split K N (fun h => B h ∨ C h) B C (fun _ _ _ hh => hh)
  linarith only [h1,h2]

end LatinonEntropy

#print axioms LatinonEntropy.history_event_mass_three_split
