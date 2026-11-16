module

public import ProfilePrincipalProbability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileFullBad {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (u : ℝ) (h : LatinHistory n) : Prop :=
  ¬historyPastLive (profileProcessGood P eps heps budget) (historyPrefix h T) ∨
    ∃ I U V : Finset (Fin n), 2*u+2*budget+2*(n : ℝ)*((n : ℝ)-T) < |profileCutObservation P I U V h|

theorem profile_full_bad_inclusion {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (hT : T ≤ n) (u : ℝ)
    (h : LatinHistory n) (hlen : h.length = n) (hbad : profileFullBad P eps heps budget T u h) :
    profilePrincipalBad P eps heps budget T u h := by
  by_contra hp
  rcases hbad with hstop | hcut
  · exact hp (Or.inl hstop)
  obtain ⟨I,U,V,hcut⟩ := hcut
  have hpre : |profileCutObservation P I U V (historyPrefix h T)| ≤ 2*u+2*budget :=
    le_of_not_gt (fun hh => hp (Or.inr ⟨I,U,V,hh⟩))
  have htail := profile_cut_observation_tail_bound P I U V h hlen T hT
  have hbound : |profileCutObservation P I U V h| ≤ 2*u+2*budget+2*(n : ℝ)*((n : ℝ)-T) := by
    calc
      _ = |profileCutObservation P I U V (historyPrefix h T)+
          (profileCutObservation P I U V h-profileCutObservation P I U V (historyPrefix h T))| := by congr 1; ring
      _ ≤ |profileCutObservation P I U V (historyPrefix h T)|+
          |profileCutObservation P I U V h-profileCutObservation P I U V (historyPrefix h T)| := abs_add_le _ _
      _ ≤ _ := add_le_add hpre htail
  exact not_lt_of_ge hbound hcut

theorem profile_full_bad_mass_le_principal {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (hT : T ≤ n) (u : ℝ)
    (K : FiniteKernel (Equiv.Perm (Fin n))) :
    historyEventMass K n (profileFullBad P eps heps budget T u) ≤
      historyEventMass K n (profilePrincipalBad P eps heps budget T u) := by
  have hs := history_event_mass_split K n (profileFullBad P eps heps budget T u)
    (profilePrincipalBad P eps heps budget T u) (fun _ => False) (fun h hh _ he =>
      Or.inl (profile_full_bad_inclusion P eps heps budget T hT u h (histories_length hh) he))
  have hz : historyEventMass K n (fun _ => False) = 0 := by simp [historyEventMass]
  simpa only [hz,add_zero] using hs

end LatinonEntropy

#print axioms LatinonEntropy.profile_full_bad_mass_le_principal
