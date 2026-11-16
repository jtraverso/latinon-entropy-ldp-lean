module

public import HistoryPrefixes
public import ProfileProcess

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileCutTolerance {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps) : ℝ :=
  (profileCorrectionParameters P eps heps).rho*eps*(n : ℝ)^2/
    (64*(profileCorrectionParameters P eps heps).upper)

theorem profile_fluid_cut_lower {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t)
    (S T : Finset (Fin n)) :
    (profileCorrectionParameters P eps heps).rho*S.card*T.card ≤ rectMass (profileRemaining P t) S T := by
  have hr : (profileCorrectionParameters P eps heps).rho ≤ P.a*eps := by
    change min 1 (P.a*eps/2) ≤ P.a*eps
    exact (min_le_right _ _).trans (by nlinarith [mul_pos P.a_pos heps])
  calc
    _ = ∑ _i ∈ S, ∑ _j ∈ T, (profileCorrectionParameters P eps heps).rho := by simp; ring
    _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ =>
      hr.trans (P.remaining_main_lower eps heps t hdegree i j)))

theorem profile_guard_failure_cut {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (h : LatinHistory n) (hv : LatinHistoryValid h)
    (hdegree : eps*n ≤ (n : ℝ)-h.length)
    (hfail : ¬CorrectableHistory (profileCorrectionParameters P eps heps) (profileCandidate P) h) :
    ∃ S T : Finset (Fin n),
      profileCutTolerance P eps heps < rectMass (profileRemaining P h.length) S T-rectMass (availability h) S T := by
  have hcut : ∃ S T : Finset (Fin n),
      rectMass (availability h) S T < (profileCorrectionParameters P eps heps).rho*S.card*T.card-
        profileCutTolerance P eps heps := by
    by_contra! hgood
    exact hfail (correctable_profile_history P eps heps h hv hdegree hgood)
  obtain ⟨S,T,hST⟩ := hcut
  refine ⟨S,T,?_⟩
  have hl := profile_fluid_cut_lower P eps heps h.length hdegree S T
  linarith only [hST,hl]

/-- At the first failure the auxiliary matrix is still the actual graph.
The deterministic main-range guard leaves only a cut deficit or the one
common stopped drift budget as the cause of failure. -/
theorem profile_first_failure_cut_or_budget {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (h : LatinHistory n)
    (hv : LatinHistoryValid h) (hdegree : eps*n ≤ (n : ℝ)-h.length)
    (hpast : historyPastLive (profileProcessGood P eps heps budget) h)
    (hstop : ¬historyLive (profileProcessGood P eps heps budget) h) :
    (∃ S T : Finset (Fin n), profileCutTolerance P eps heps <
      rectMass (profileRemaining P h.length) S T-
      rectMass (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h) S T) ∨
    budget < pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
  rcases latinStopped_first_failure P.npos (profileCorrectionParameters P eps heps)
      (profileCandidate P) budget h hpast hstop with hc | hb
  · left
    obtain ⟨S,T,hcut⟩ := profile_guard_failure_cut P eps heps h hv hdegree hc
    refine ⟨S,T,?_⟩
    have he : rectMass (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h) S T =
        rectMass (availability h) S T :=
      congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => rectMass Q S T)
        (stoppedAvailability_eq_pastLive (profileProcessGood P eps heps budget)
          (fun t i j => profileHazard P t i j) h hpast)
    rw [he]
    exact hcut
  · right
    have he : (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) =
        (fun g (_ : Equiv.Perm (Fin n)) => if historyLive (profileProcessGood P eps heps budget) g
          then proposedRowDrift P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) g else 0) := by
      funext g a
      exact profile_cost_matches_stopped_proposal P eps heps budget g
    rw [he]
    exact hb

end LatinonEntropy

#print axioms LatinonEntropy.profile_first_failure_cut_or_budget
