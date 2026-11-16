module

public import ProfilePrincipalCuts
public import HistoryEventBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileAvailabilityNoiseEvent {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (h : LatinHistory n) : Prop :=
  ∃ t : Fin T, ∃ U V : Finset (Fin n), profileCutTolerance P eps heps/2 ≤
    |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) (profileCutTest P t.val U V)) h|

def profileMonitorNoiseEvent {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (u : ℝ) (h : LatinHistory n) : Prop :=
  ∃ I U V : Finset (Fin n), u ≤
    |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h|

def profilePrincipalBad {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (u : ℝ) (h : LatinHistory n) : Prop :=
  ¬historyPastLive (profileProcessGood P eps heps budget) (historyPrefix h T) ∨
    ∃ I U V : Finset (Fin n), 2*u+2*budget < |profileCutObservation P I U V (historyPrefix h T)|

theorem profile_principal_bad_inclusion {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (v : ℝ) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (hvsmall : v ≤ profileCutTolerance P eps heps/2) (u : ℝ)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (hT : T ≤ h.length)
    (hbad : profilePrincipalBad P eps heps v T u h) :
    v ≤ profileMainBudget P eps heps v T h ∨
      profileAvailabilityNoiseEvent P eps heps v T h ∨ profileMonitorNoiseEvent P eps heps v T u h := by
  by_cases hB : v ≤ profileMainBudget P eps heps v T h
  · exact Or.inl hB
  by_cases hA : profileAvailabilityNoiseEvent P eps heps v T h
  · exact Or.inr (Or.inl hA)
  by_cases hM : profileMonitorNoiseEvent P eps heps v T u h
  · exact Or.inr (Or.inr hM)
  have hpast : historyPastLive (profileProcessGood P eps heps v) (historyPrefix h T) := by
    by_contra hstop
    rcases profile_main_failure_inclusion P eps heps v T hdegree hvsmall h hv hT hstop with hb | ha
    · exact hB hb
    · exact hA ha
  rcases hbad with hstop | hcut
  · exact False.elim (hstop hpast)
  obtain ⟨I,U,V,hcut⟩ := hcut
  have hnoise : |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps v)
      (profileProcessGood P eps heps v) (profileMonitorTest P T I U V)) h| ≤ u :=
    (lt_of_not_ge (fun hh => hM ⟨I,U,V,hh⟩)).le
  have hb := profile_principal_cut_bound P eps heps v T I U V h hv hT hpast v u
    (lt_of_not_ge hB).le hnoise
  exact False.elim (not_lt_of_ge hb hcut)

set_option backward.isDefEq.respectTransparency false in
/-- Joint survival and principal-profile control, with the common drift
budget paid only once across both families of exponentially many tests. -/
theorem profile_principal_bad_mass_le {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (v : ℝ) (hv : 0 < v) (T : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-T) (hvsmall : v ≤ profileCutTolerance P eps heps/2)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ (n : ℝ)*(2*(n : ℝ))) :
    historyEventMass ((profileProcessPolicy P eps heps v).kernel P.npos) n (profilePrincipalBad P eps heps v T u) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v+
        ((T : ℝ)*((2 : ℝ)^n)^2)*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-
          (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ))))))+
        (8 : ℝ)^n*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
  let K := (profileProcessPolicy P eps heps v).kernel P.npos
  have hTn := (P.main_index eps heps T hdegree).le
  have hB : historyEventMass K n (fun h => v ≤ profileMainBudget P eps heps v T h) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v := by
    simpa only [K,historyEventMass,history_event_indicator_canonical,profileMainBudget] using
      profile_full_history_budget_markov P eps heps v m hm hsize T n hTn hdegree v hv
  have hA : historyEventMass K n (profileAvailabilityNoiseEvent P eps heps v T) ≤
      ((T : ℝ)*((2 : ℝ)^n)^2)*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-
        (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
    simpa only [K,historyEventMass,history_event_indicator_canonical,profileAvailabilityNoiseEvent] using
      profile_simultaneous_cut_noise P eps heps v m hm hsize T (profileCutTolerance P eps heps/2)
        (half_pos (profileCutTolerance_pos P eps heps)).le (profile_cut_threshold_admissible P eps heps T hdegree)
  have hM : historyEventMass K n (profileMonitorNoiseEvent P eps heps v T u) ≤
      (8 : ℝ)^n*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
    simpa only [K,historyEventMass,history_event_indicator_canonical,profileMonitorNoiseEvent] using
      profile_simultaneous_monitor_noise P eps heps v m hm hsize T u hu0 hu
  have hs := history_event_mass_three_split K n (profilePrincipalBad P eps heps v T u)
    (fun h => v ≤ profileMainBudget P eps heps v T h) (profileAvailabilityNoiseEvent P eps heps v T)
    (profileMonitorNoiseEvent P eps heps v T u) (fun h hh hp hbad =>
      profile_principal_bad_inclusion P eps heps v T hdegree hvsmall u h
        ((profileProcessPolicy P eps heps v).positive_history_valid P.npos n le_rfl h hh hp)
        (by rw [histories_length hh]; exact hTn) hbad)
  exact hs.trans (add_le_add (add_le_add hB hA) hM)

end LatinonEntropy

#print axioms LatinonEntropy.profile_principal_bad_mass_le
