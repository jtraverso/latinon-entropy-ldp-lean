module

public import UniformProfileSurvival
public import RowLogBands

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

theorem log_squared_rate_times_affine_log {f : ℕ → ℝ}
    (hf : Tendsto (fun n : ℕ => f n*Real.log (n : ℝ)^2) atTop (𝓝 0)) (A B : ℝ) :
    Tendsto (fun n : ℕ => f n*(A*Real.log (n : ℝ)+B)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have haux := (hinv.const_mul A).add ((hinv.pow 2).const_mul B)
  have hprod := hf.mul haux
  have heq : (fun n : ℕ => f n*(A*Real.log (n : ℝ)+B)) =ᶠ[atTop]
      (fun n : ℕ => (f n*Real.log (n : ℝ)^2)*
        (A*(Real.log (n : ℝ))⁻¹+B*((Real.log (n : ℝ))⁻¹)^2)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog := (Real.log_pos hnR).ne'
    field_simp [hlog]
  exact Filter.Tendsto.congr' heq.symm (by simpa using hprod)

def fixedEntropyLogConstant (a b eps : ℝ) : ℝ :=
  |Real.log (min (a/2) (1/4))|+|Real.log (fixedCorrectionUpper a b eps)|

theorem profile_entropy_log_constant_fixed {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b) :
    rowEntropyLogConstant (profileCorrectionParameters P eps heps) =
      fixedEntropyLogConstant a b eps := by
  unfold rowEntropyLogConstant fixedEntropyLogConstant
  rw [profile_upper_fixed P a b eps heps ha hb]
  simp only [RowCorrectionParameters.lower,profileCorrectionParameters,ha]

def profileEntropyRate (a b eps : ℝ) (m n : ℕ) : ℝ :=
  profileDriftRate (b/(a*eps)) m n*
      (((b/(a*eps))+1)*Real.log (n : ℝ)+(b/(a*eps))*|Real.log a|+
        2*fixedEntropyLogConstant a b eps+1)+
    profileSurvivalRate a b eps m n*((b/(a*eps))*Real.log (n : ℝ)+
      (b/(a*eps))*|Real.log a|)+Real.log (n : ℝ)/(n : ℝ)

theorem profile_entropy_rate_tendsto_zero (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (m : ℕ) :
    Tendsto (fun n : ℕ => profileEntropyRate a b eps m n) atTop (𝓝 0) := by
  have h1 := log_squared_rate_times_affine_log
    (profile_drift_rate_log_sq_tendsto_zero (b/(a*eps)) m) ((b/(a*eps))+1)
    ((b/(a*eps))*|Real.log a|+2*fixedEntropyLogConstant a b eps+1)
  have h2 := log_squared_rate_times_affine_log
    (profile_survival_rate_log_sq_tendsto_zero a b eps ha heps m) (b/(a*eps))
    ((b/(a*eps))*|Real.log a|)
  have h3 : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 1)).tendsto_div_nhds_zero
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact hr.comp hcast
  simpa [profileEntropyRate,add_assoc] using (h1.add h2).add h3

end LatinonEntropy

#print axioms LatinonEntropy.profile_entropy_rate_tendsto_zero
