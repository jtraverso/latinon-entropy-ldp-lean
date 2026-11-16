module

public import HistoryTruncation
public import ProfileCutFailure
public import ProfileCutNoiseValue

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileMainBudget {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (h : LatinHistory n) : ℝ :=
  pathSum (truncateIncrement T (fun g (_ : Equiv.Perm (Fin n)) =>
    profileActualDriftCost P eps heps budget g)) h

theorem profile_prefix_budget_le_main {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (h : LatinHistory n)
    (hT : T ≤ h.length) (t : ℕ) (ht : t ≤ T) :
    pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g)
      (historyPrefix h t) ≤ profileMainBudget P eps heps budget T h := by
  unfold profileMainBudget
  rw [pathSum_truncate_prefix T _ h hT]
  have hb := pathSum_prefix_le
    (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g)
    (fun g _ => profileActualDriftCost_nonneg P eps heps budget g)
    (historyPrefix h T) t (by rw [historyPrefix_length h T hT]; exact ht)
  rw [historyPrefix_nested h T t ht hT] at hb
  exact hb

/-- Event inclusion for premature stopping. It uses the actual profile,
cut guard, drift and martingale; no survival or cut-preservation hypothesis
is supplied. The full history only needs to be valid. -/
theorem profile_main_failure_inclusion {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (v : ℝ) (T : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-T) (hvsmall : v ≤ profileCutTolerance P eps heps/2)
    (h : LatinHistory n) (hvalid : LatinHistoryValid h) (hT : T ≤ h.length)
    (hbad : ¬historyPastLive (profileProcessGood P eps heps v) (historyPrefix h T)) :
    v ≤ profileMainBudget P eps heps v T h ∨
      ∃ t : Fin T, ∃ U V : Finset (Fin n), profileCutTolerance P eps heps/2 ≤
        |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps v)
          (profileProcessGood P eps heps v) (profileCutTest P t.val U V)) h| := by
  by_cases hbudget : v ≤ profileMainBudget P eps heps v T h
  · exact Or.inl hbudget
  · right
    have hbudgetlt := lt_of_not_ge hbudget
    obtain ⟨t,ht,hpast,hstop⟩ := history_first_failure (profileProcessGood P eps heps v) (historyPrefix h T) hbad
    rw [historyPrefix_length h T hT] at ht
    rw [historyPrefix_nested h T t ht.le hT] at hpast hstop
    have htn : t ≤ h.length := ht.le.trans hT
    have hlen := historyPrefix_length h t htn
    have hdeg : eps*n ≤ (n : ℝ)-(historyPrefix h t).length := by
      rw [hlen]
      have htR : (t : ℝ) ≤ T := Nat.cast_le.mpr ht.le
      linarith only [hdegree,htR]
    have hv := valid_historyPrefix h hvalid t htn
    have hcost := profile_prefix_budget_le_main P eps heps v T h hT t ht.le
    rcases profile_first_failure_cut_or_budget P eps heps v (historyPrefix h t) hv hdeg hpast hstop with hcut | hb
    · obtain ⟨U,V,hUV⟩ := hcut
      refine ⟨⟨t,ht⟩,U,V,?_⟩
      have hd := profile_cut_defect_decomposition P (profileProcessPolicy P eps heps v)
        (profileProcessGood P eps heps v) U V (historyPrefix h t) hv
      have hdrift := profile_cut_drift_path_bound P eps heps v t U V (historyPrefix h t)
      rw [hlen] at hUV hd
      have hidentity := profile_cut_noise_prefix_identity P t (profileProcessPolicy P eps heps v)
        (profileProcessGood P eps heps v) U V h htn
      rw [hidentity]
      have hsign := le_abs_self (pathSum (profileCutDriftIncrement P t (profileProcessPolicy P eps heps v)
        (profileProcessGood P eps heps v) U V) (historyPrefix h t))
      have hn := le_abs_self (pathSum (profileCutNoiseIncrement P t (profileProcessPolicy P eps heps v)
        (profileProcessGood P eps heps v) U V) (historyPrefix h t))
      linarith only [hUV,hd,hdrift,hcost,hbudgetlt,hvsmall,hsign,hn]
    · exact False.elim (not_lt_of_ge (hcost.trans (le_of_lt hbudgetlt)) hb)

end LatinonEntropy

#print axioms LatinonEntropy.profile_main_failure_inclusion
