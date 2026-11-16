module

public import ProfileJointRates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology Finset
open scoped Classical

def profileCutClose {n : ℕ} (P : PositiveLatinProfile n) (h : LatinHistory n) (eta : ℝ) : Prop :=
  ∀ I U V : Finset (Fin n), |profileCutObservation P I U V h| ≤ eta*(n : ℝ)^2

def profileApproximationBad {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) (eta : ℝ) (h : LatinHistory n) : Prop :=
  ¬historyPastLive (profileProcessGood P eps heps budget) (historyPrefix h T) ∨ ¬profileCutClose P h eta

theorem profile_approximation_bad_mass_le_full {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (u eta : ℝ)
    (hth : 2*u+2*budget+2*(n : ℝ)*((n : ℝ)-T) ≤ eta*(n : ℝ)^2)
    (K : FiniteKernel (Equiv.Perm (Fin n))) :
    historyEventMass K n (profileApproximationBad P eps heps budget T eta) ≤
      historyEventMass K n (profileFullBad P eps heps budget T u) := by
  have hsplit : ∀ h ∈ histories (Equiv.Perm (Fin n)) n, 0 < historyWeight K h →
      profileApproximationBad P eps heps budget T eta h → profileFullBad P eps heps budget T u h ∨ False := by
    intro h _ _ hbad
    left
    rcases hbad with hstop | hcut
    · exact Or.inl hstop
    · right
      change ¬∀ I U V : Finset (Fin n), |profileCutObservation P I U V h| ≤ eta*(n : ℝ)^2 at hcut
      push Not at hcut
      obtain ⟨I,U,V,hcut⟩ := hcut
      exact ⟨I,U,V,hth.trans_lt hcut⟩
  have hs := history_event_mass_split K n (profileApproximationBad P eps heps budget T eta)
    (profileFullBad P eps heps budget T u) (fun _ => False) hsplit
  have hz : historyEventMass K n (fun _ => False) = 0 := by simp [historyEventMass]
  simpa only [hz,add_zero] using hs

/-- The actual full Latin history follows every three-dimensional cut of
its prescribed tensor, with an error tending to zero with eps. Survival
and closeness are controlled jointly, uniformly over profiles with fixed bounds. -/
theorem eventually_uniform_profile_closeness (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      historyEventMass
        ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) n
        (profileApproximationBad P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4) (mainRange eps n) (4*eps)) ≤
        1/Real.log (n : ℝ)^2 := by
  obtain ⟨m,hm⟩ := fixed_permanent_cap_index_exists a b eps
  have hsmall := (tendsto_order.mp (profile_closeness_rate_log_sq_tendsto_zero a b eps ha heps m)).2 1 (by norm_num)
  filter_upwards [hsmall,eventually_permanentCapError_le_half m,eventually_ge_atTop 2,
    eventually_ge_atTop ⌈(2 : ℝ)/eps⌉₊] with n hs hsize hn hnceil
  intro P hPa hPb
  have hn1 : (1 : ℝ) < n := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hn2]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsq : 0 < Real.log (n : ℝ)^2 := sq_pos_of_pos hlog
  have hdiv : (2 : ℝ)/eps ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hnceil)
  have hTwo : 2 ≤ eps*(n : ℝ) := by nlinarith only [(div_le_iff₀ heps).mp hdiv]
  have hth := main_range_full_error_le_four_eps a b eps ha heps heps1 n hTwo
  have happrox := profile_approximation_bad_mass_le_full P eps heps
    (fixedCutDensity a b eps*(n : ℝ)^2/4) (mainRange eps n) (eps*(n : ℝ)^2/8) (4*eps) hth
    ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos)
  have hfull := profile_full_bad_rate_bound P a b eps heps heps1 hPa hPb m hm hsize
    (mainRange eps n) (mainRange_degree eps heps1 n)
  exact happrox.trans (hfull.trans (le_of_lt ((lt_div_iff₀ hsq).mpr hs)))

end LatinonEntropy

#print axioms LatinonEntropy.eventually_uniform_profile_closeness
