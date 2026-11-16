module

public import HistoryEntropy
public import HistoryEventBounds
public import FiniteEntropyCount

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem sum_history_atoms {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T : ℕ) (F : List Ω → ℝ) :
    (∑ h : {h // h ∈ histories Ω T}, F h.val) = ∑ h ∈ histories Ω T, F h := by
  rw [← attach_eq_univ,sum_attach]

/-- Histories are counted as elements of their finite ambient space.
This representation retains every ordered row and introduces no quotient. -/
def goodHistoryAtoms {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T : ℕ) (Good : List Ω → Prop) : Finset {h // h ∈ histories Ω T} :=
  univ.filter (fun h => Good h.val)

theorem history_entropy_to_good_count {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (Good : List Ω → Prop) (L : ℝ)
    (hbad : historyEventMass K T (fun h => ¬Good h) < 1)
    (hcap : ((histories Ω T).card : ℝ)*Real.exp (-L) ≤ 1) :
    historyEntropy K T-historyEventMass K T (fun h => ¬Good h)*L-Real.log 2 ≤
      Real.log ((goodHistoryAtoms (Ω := Ω) T Good).card : ℝ) := by
  let I := {h // h ∈ histories Ω T}
  let p : I → ℝ := fun h => historyWeight K h.val
  have htotal : ∑ h : I, p h = 1 := by
    dsimp only [p]
    rw [sum_history_atoms]
    exact historyWeight_total K T
  have hS : (goodHistoryAtoms (Ω := Ω) T Good).Nonempty := by
    by_contra he
    have hnone : ∀ h ∈ histories Ω T, ¬Good h := by
      intro h hh hg
      exact he ⟨⟨h,hh⟩,mem_filter.mpr ⟨mem_univ _,hg⟩⟩
    have hm : historyEventMass K T (fun h => ¬Good h) = 1 := by
      calc
        _ = ∑ h ∈ histories Ω T, historyWeight K h := by
          apply sum_congr rfl
          intro h hh
          simp only [hnone h hh,not_false_eq_true,ite_true]
        _ = 1 := historyWeight_total K T
    linarith only [hm,hbad]
  have hcapI : (Fintype.card I : ℝ)*Real.exp (-L) ≤ 1 := by
    simpa only [I,Fintype.card_coe] using hcap
  have h := finite_entropy_to_good_count p (fun h => historyWeight_nonneg K h.val)
    htotal (goodHistoryAtoms (Ω := Ω) T Good) hS L hcapI
  have hE : -(∑ h : I, p h*Real.log (p h)) = historyEntropy K T := by
    dsimp only [p]
    rw [sum_history_atoms T (fun h => historyWeight K h*Real.log (historyWeight K h))]
    rfl
  have hB : (∑ h : I, if h ∈ goodHistoryAtoms (Ω := Ω) T Good then 0 else p h) =
      historyEventMass K T (fun h => ¬Good h) := by
    simp only [goodHistoryAtoms,mem_filter,mem_univ,true_and,p,historyEventMass]
    rw [sum_history_atoms T (fun h => if Good h then 0 else historyWeight K h)]
    apply sum_congr rfl
    intro h _
    by_cases hg : Good h
    · simp only [hg,ite_true,not_true_eq_false,ite_false]
    · simp only [hg,ite_false,not_false_eq_true,ite_true]
  rw [hE,hB] at h
  exact h

end LatinonEntropy

#print axioms LatinonEntropy.history_entropy_to_good_count
