module

public import ProfileMonitorValues
public import ProfileSurvivalEvent
public import ProfileObservationCuts

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem profile_principal_cut_decomposition {n : ℕ} (P : PositiveLatinProfile n)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (I U V : Finset (Fin n))
    (h : LatinHistory n) (hv : LatinHistoryValid h) (hpast : historyPastLive Good h) :
    profileCutObservation P I U V h =
      pathSum (profileMonitorNoise P h.length S Good I U V) h+
        pathSum (profileMonitorDrift P h.length S Good I U V) h := by
  calc
    _ = ∑ i ∈ U, ∑ j ∈ V, pathSum (fun g sigma =>
        timeCutWeight I g.length*profileCellObservation P g sigma i j) h := by
      unfold profileCutObservation profileCutObservationIncrement
      rw [pathSum_sum]
      apply sum_congr rfl
      intro i _
      rw [pathSum_sum]
    _ = ∑ i ∈ U, ∑ j ∈ V, pathSum (fun g sigma =>
        profileMonitorWeight P h.length I g.length i j*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      exact profile_observation_monitor_identity P Good (fun g => permanentMarginal (S.matrix g))
        (timeCutWeight I) h hv hpast i j
    _ = pathSum (fun g sigma => ∑ i ∈ U, ∑ j ∈ V,
        profileMonitorWeight P h.length I g.length i j*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by
      rw [pathSum_sum]
      apply sum_congr rfl
      intro i _
      rw [pathSum_sum]
    _ = pathSum (fun g sigma => profileMonitorNoise P h.length S Good I U V g sigma+
        profileMonitorDrift P h.length S Good I U V g sigma) h := by
      apply pathSum_congr
      intro g sigma
      simp only [profileMonitorNoise,profileMonitorDrift,profileCellError,mul_add,sum_add_distrib]
    _ = _ := pathSum_add _ _ _

theorem profile_principal_cut_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (I U V : Finset (Fin n))
    (h : LatinHistory n) (hv : LatinHistoryValid h) (hT : T ≤ h.length)
    (hpast : historyPastLive (profileProcessGood P eps heps budget) (historyPrefix h T))
    (v u : ℝ) (hbudget : profileMainBudget P eps heps budget T h ≤ v)
    (hnoise : |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h| ≤ u) :
    |profileCutObservation P I U V (historyPrefix h T)| ≤ 2*u+2*v := by
  have hlen := historyPrefix_length h T hT
  have hdecomp := profile_principal_cut_decomposition P (profileProcessPolicy P eps heps budget)
    (profileProcessGood P eps heps budget) I U V (historyPrefix h T) (valid_historyPrefix h hv T hT) hpast
  rw [hlen] at hdecomp
  have hidentity := profile_monitor_noise_prefix_identity P T (profileProcessPolicy P eps heps budget)
    (profileProcessGood P eps heps budget) I U V h hT
  have hnEq : pathSum (profileMonitorNoise P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) I U V) (historyPrefix h T) =
      2*pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps budget)
        (profileProcessGood P eps heps budget) (profileMonitorTest P T I U V)) h := by linarith only [hidentity]
  have hnBound : |pathSum (profileMonitorNoise P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) I U V) (historyPrefix h T)| ≤ 2*u := by
    rw [hnEq,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hnoise (by norm_num)
  have hd := profile_monitor_drift_path_bound P eps heps budget T I U V (historyPrefix h T)
  have hc := profile_prefix_budget_le_main P eps heps budget T h hT T le_rfl
  have hdBound : |pathSum (profileMonitorDrift P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) I U V) (historyPrefix h T)| ≤ 2*v := by
    exact hd.trans (mul_le_mul_of_nonneg_left (hc.trans hbudget) (by norm_num))
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hnBound hdBound)

end LatinonEntropy

#print axioms LatinonEntropy.profile_principal_cut_bound
