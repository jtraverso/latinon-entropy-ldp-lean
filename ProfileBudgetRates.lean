module

public import DriftBudgetAsymptotics
public import ProfileDefectStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

theorem sqrt_scaled_div {x e : ℝ} (hx : 0 < x) (he : 0 ≤ e) :
    Real.sqrt (2*x*e)/x = Real.sqrt 2*Real.sqrt (e/x) := by
  have hp : 0 ≤ 2*x*e := by positivity
  have hh : Real.sqrt ((2*x*e)/x^2) = Real.sqrt (2*x*e)/x := by
    rw [Real.sqrt_div hp,Real.sqrt_sq hx.le]
  calc
    _ = Real.sqrt ((2*x*e)/x^2) := hh.symm
    _ = Real.sqrt (2*(e/x)) := congrArg Real.sqrt (by field_simp)
    _ = _ := Real.sqrt_mul (by norm_num) _

theorem sqrt_div_self {x : ℝ} (hx : 0 < x) : Real.sqrt x/x = Real.sqrt (1/x) := by
  have hh : Real.sqrt (x/x^2) = Real.sqrt x/x := by rw [Real.sqrt_div hx.le,Real.sqrt_sq hx.le]
  rw [← hh]
  congr 1
  field_simp

def profileDriftRate (c : ℝ) (m n : ℕ) : ℝ :=
  (1+6*c*Real.exp (6*c))*Real.sqrt 2*Real.sqrt (permanentCapError m n/(n : ℝ))+
    6*c*Real.exp (6*c)*Real.sqrt (1/(n : ℝ))

theorem profile_normalized_drift_bound_identity {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (m : ℕ) :
    (Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/(n : ℝ) =
      profileDriftRate (P.b/(P.a*eps)) m n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have he := permanentCapError_nonneg n m P.npos
  unfold profileStabilityBound profileDriftRate
  calc
    _ = (1+6*(P.b/(P.a*eps))*Real.exp (6*(P.b/(P.a*eps))))*
        (Real.sqrt (2*(n : ℝ)*permanentCapError m n)/(n : ℝ))+
      6*(P.b/(P.a*eps))*Real.exp (6*(P.b/(P.a*eps)))*(Real.sqrt (n : ℝ)/(n : ℝ)) := by ring
    _ = _ := by rw [sqrt_scaled_div hn he,sqrt_div_self hn]; ring

theorem profile_drift_rate_log_sq_tendsto_zero (c : ℝ) (m : ℕ) :
    Tendsto (fun n : ℕ => profileDriftRate c m n*Real.log (n : ℝ)^2) atTop (𝓝 0) := by
  have h1 := (permanent_error_sqrt_log_sq_tendsto_zero m).const_mul
    ((1+6*c*Real.exp (6*c))*Real.sqrt 2)
  have h2 := sqrt_inverse_log_sq_tendsto_zero.const_mul (6*c*Real.exp (6*c))
  have he : (fun n : ℕ => profileDriftRate c m n*Real.log (n : ℝ)^2) =
      (fun n : ℕ => ((1+6*c*Real.exp (6*c))*Real.sqrt 2)*
        (Real.sqrt (permanentCapError m n/(n : ℝ))*Real.log (n : ℝ)^2)+
        (6*c*Real.exp (6*c))*(Real.sqrt (1/(n : ℝ))*Real.log (n : ℝ)^2)) := by
    funext n
    unfold profileDriftRate
    ring
  rw [he]
  simpa using h1.add h2

end LatinonEntropy

#print axioms LatinonEntropy.profile_normalized_drift_bound_identity
#print axioms LatinonEntropy.profile_drift_rate_log_sq_tendsto_zero
