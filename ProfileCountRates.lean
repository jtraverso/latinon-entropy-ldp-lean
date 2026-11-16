module

public import EntropyRateAsymptotics
public import ProfileJointRates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

def profileCountRate (a b eps : ℝ) (m n : ℕ) : ℝ :=
  profileEntropyRate a b eps m n+profileClosenessRate a b eps m n*Real.log (n : ℝ)+
    Real.log 2/(n : ℝ)^2

theorem profile_closeness_rate_tendsto_zero (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (m : ℕ) :
    Tendsto (fun n : ℕ => profileClosenessRate a b eps m n) atTop (𝓝 0) := by
  simpa using log_squared_rate_times_affine_log
    (profile_closeness_rate_log_sq_tendsto_zero a b eps ha heps m) 0 1

theorem profile_count_rate_tendsto_zero (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (m : ℕ) :
    Tendsto (fun n : ℕ => profileCountRate a b eps m n) atTop (𝓝 0) := by
  have h1 := profile_entropy_rate_tendsto_zero a b eps ha heps m
  have h2 : Tendsto (fun n : ℕ => profileClosenessRate a b eps m n*Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa using log_squared_rate_times_affine_log
      (profile_closeness_rate_log_sq_tendsto_zero a b eps ha heps m) 1 0
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hinv.pow 2).const_mul (Real.log 2)
  simpa [profileCountRate] using (h1.add h2).add h3

end LatinonEntropy

#print axioms LatinonEntropy.profile_count_rate_tendsto_zero
