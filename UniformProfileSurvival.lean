module

public import ProfileFiniteRates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology Finset
open scoped Classical

theorem profile_survival_rate_log_sq_tendsto_zero (a b eps : ℝ) (ha : 0 < a) (heps : 0 < eps) (m : ℕ) :
    Tendsto (fun n : ℕ => profileSurvivalRate a b eps m n*Real.log (n : ℝ)^2) atTop (𝓝 0) := by
  have hd := fixedCutDensity_pos a b eps ha heps
  have h1 := (profile_drift_rate_log_sq_tendsto_zero (b/(a*eps)) m).const_mul (4/fixedCutDensity a b eps)
  have h2 := exponential_union_rate_log_sq_tendsto_zero 4 ((fixedCutDensity a b eps)^2/16)
    (div_pos (sq_pos_of_pos hd) (by norm_num)) m
  have he : (fun n : ℕ => profileSurvivalRate a b eps m n*Real.log (n : ℝ)^2) =
      (fun n : ℕ => (4/fixedCutDensity a b eps)*(profileDriftRate (b/(a*eps)) m n*Real.log (n : ℝ)^2)+
        exponentialUnionRate 4 ((fixedCutDensity a b eps)^2/16) m n*Real.log (n : ℝ)^2) := by
    funext n; unfold profileSurvivalRate; ring
  rw [he]
  simpa using h1.add h2

/-- Uniform over all positive tri-stochastic tensors with fixed bounds.
The process, cap index, size condition, degree and logarithmic rate are
all discharged rather than supplied as asymptotic hypotheses. -/
theorem eventually_uniform_profile_survival (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
        if ¬historyPastLive (profileProcessGood P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4))
            (historyPrefix h (mainRange eps n))
        then historyWeight ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) h else 0) ≤
        1/Real.log (n : ℝ)^2 := by
  obtain ⟨m,hm⟩ := fixed_permanent_cap_index_exists a b eps
  have hsmall := (tendsto_order.mp (profile_survival_rate_log_sq_tendsto_zero a b eps ha heps m)).2 1 (by norm_num)
  filter_upwards [hsmall,eventually_permanentCapError_le_half m,eventually_ge_atTop 2] with n hs hsize hn
  intro P hPa hPb
  have hn1 : (1 : ℝ) < n := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hn2]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsq : 0 < Real.log (n : ℝ)^2 := sq_pos_of_pos hlog
  have hbound := profile_survival_rate_bound P a b eps heps hPa hPb m hm hsize
    (mainRange eps n) (mainRange_degree eps heps1 n)
  exact hbound.trans (le_of_lt ((lt_div_iff₀ hsq).mpr hs))

end LatinonEntropy

#print axioms LatinonEntropy.eventually_uniform_profile_survival
