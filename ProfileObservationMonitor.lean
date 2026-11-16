module

public import HistoryMonitorIdentity
public import ProfileProcess

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

def profileCellObservation {n : ℕ} (P : PositiveLatinProfile n) (g : LatinHistory n)
    (sigma : Equiv.Perm (Fin n)) (i j : Fin n) : ℝ :=
  if ht : g.length < n then rowPermutationMatrix sigma i j-P.p ⟨g.length,ht⟩ i j else 0

theorem profile_observation_live {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (g : LatinHistory n) (hlive : historyLive Good g) (ht : g.length < n)
    (sigma : Equiv.Perm (Fin n)) (i j : Fin n) :
    profileCellObservation P g sigma i j = profileCellError P Good m g sigma i j+
      profileHazard P g.length i j*profileCellDefect P Good g i j := by
  have hB := congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => Q i j)
    (stoppedAvailability_eq_live Good (fun t i j => profileHazard P t i j) g hlive)
  have hp := P.remaining_hazard g.length ht i j
  simp only [profileCellObservation,ht,dite_true,profileCellError,killedRowNoise,killedRowDrift,
    hlive,ite_true,profileCellDefect]
  rw [hB]
  linear_combination hp

theorem pathSum_congr_live_before {Ω : Type*} (Good : List Ω → Prop)
    (X Y : List Ω → Ω → ℝ) (T : ℕ)
    (heq : ∀ g, historyLive Good g → g.length < T → ∀ a, X g a = Y g a)
    (h : List Ω) (hpast : historyPastLive Good h) (hlen : h.length ≤ T) :
    pathSum X h = pathSum Y h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    have hlive : historyLive Good h := hpast
    have ht : h.length < T := by simp only [List.length_cons] at hlen; omega
    rw [pathSum,pathSum,ih (historyLive_pastLive Good h hlive) ht.le,heq h hlive ht a]

/-- On a surviving principal prefix, the transformed errors are exactly
the observed Latin rows centered at the prescribed tensor. -/
theorem profile_observation_monitor_identity {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (w : ℕ → ℝ) (h : LatinHistory n) (hv : LatinHistoryValid h)
    (hpast : historyPastLive Good h) (i j : Fin n) :
    pathSum (fun g sigma => w g.length*profileCellObservation P g sigma i j) h =
      pathSum (fun g sigma => hazardMonitor (fun t => profileHazard P t i j) w g.length h.length*
        profileCellError P Good m g sigma i j) h := by
  calc
    _ = pathSum (fun g sigma => w g.length*(profileCellError P Good m g sigma i j+
        profileHazard P g.length i j*profileCellDefect P Good g i j)) h := by
      apply pathSum_congr_live_before Good _ _ n ?_ h hpast (valid_history_length_le P.npos hv)
      intro g hlive ht sigma
      rw [profile_observation_live P Good m g hlive ht sigma i j]
    _ = _ := profile_cell_monitor_identity P Good m w h hv i j

end LatinonEntropy

#print axioms LatinonEntropy.profile_observation_monitor_identity
