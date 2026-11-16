module

public import ProfileFiniteCount
public import ProfileCountRates
public import ProfileEntropyRateBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

theorem profile_finite_latin_history_count_rate {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (hTwo : 2 ≤ eps*(n : ℝ))
    (hsmall : profileClosenessRate a b eps m n < 1) :
    profileEntropy P-2*(n : ℝ)^2-(n : ℝ)^2*profileCountRate a b eps m n ≤
      Real.log ((profileLatinHistoryAtoms P (4*eps)).card : ℝ) := by
  have hcount := profile_finite_latin_history_count P a b eps heps heps1 ha hb m hm hsize hTwo hsmall
  have herr := profile_entropy_error_le_rate P a b eps heps ha hb m
  have hn : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr P.npos).ne'
  have he : (n : ℝ)^2*profileCountRate a b eps m n =
      (n : ℝ)^2*profileEntropyRate a b eps m n+
        profileClosenessRate a b eps m n*((n : ℝ)^2*Real.log (n : ℝ))+Real.log 2 := by
    unfold profileCountRate
    field_simp [hn]
  rw [he]
  linarith only [hcount,herr]

/-- The finite entropy lower bound, uniform over all positive
tri-stochastic tensors with fixed bounds a,b. -/
theorem eventually_uniform_profile_history_count (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : PositiveLatinProfile n), P.a = a → P.b = b →
      profileEntropy P-2*(n : ℝ)^2-eta*(n : ℝ)^2 ≤
        Real.log ((profileLatinHistoryAtoms P (4*eps)).card : ℝ) := by
  obtain ⟨m,hm⟩ := fixed_permanent_cap_index_exists a b eps
  have hsmall := (tendsto_order.mp (profile_count_rate_tendsto_zero a b eps ha heps m)).2 eta heta
  have hprob := (tendsto_order.mp (profile_closeness_rate_tendsto_zero a b eps ha heps m)).2 1 (by norm_num)
  filter_upwards [hsmall,hprob,eventually_permanentCapError_le_half m,
    eventually_ge_atTop ⌈(2 : ℝ)/eps⌉₊] with n hs hp hsize hnceil
  intro P hPa hPb
  have hdiv : (2 : ℝ)/eps ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hnceil)
  have hTwo : 2 ≤ eps*(n : ℝ) := by nlinarith only [(div_le_iff₀ heps).mp hdiv]
  have h := profile_finite_latin_history_count_rate P a b eps heps heps1 hPa hPb m hm hsize hTwo hp
  have hmultiply := mul_le_mul_of_nonneg_left hs.le (sq_nonneg (n : ℝ))
  nlinarith only [h,hmultiply]

end LatinonEntropy

#print axioms LatinonEntropy.eventually_uniform_profile_history_count
