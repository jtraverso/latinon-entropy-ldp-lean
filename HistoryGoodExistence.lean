module

public import HistoryEntropyCount

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem goodHistoryAtoms_nonempty_of_bad_mass_lt_one
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (K : FiniteKernel Ω)
    (T : ℕ) (Good : List Ω → Prop)
    (hbad : historyEventMass K T (fun h => ¬Good h) < 1) :
    (goodHistoryAtoms (Ω := Ω) T Good).Nonempty := by
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

end LatinonEntropy

#print axioms LatinonEntropy.goodHistoryAtoms_nonempty_of_bad_mass_lt_one
