module

public import PermanentAsymptotics
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

theorem permanent_error_log_fourth_div_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ => permanentCapError m n*Real.log (n : ℝ)^4/(n : ℝ)) atTop (𝓝 0) := by
  have h4 : Tendsto (fun n : ℕ => Real.log (n : ℝ)^4/(n : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h5 : Tendsto (fun n : ℕ => Real.log (n : ℝ)^5/(n : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 5)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have he : (fun n : ℕ => permanentCapError m n*Real.log (n : ℝ)^4/(n : ℝ)) =
      (fun n : ℕ => ((m : ℝ)+1)*(Real.log (n : ℝ)^5/(n : ℝ))+
        ((m : ℝ)*(m+1)+1)*(Real.log (n : ℝ)^4/(n : ℝ))) := by
    funext n
    unfold permanentCapError
    ring
  rw [he]
  simpa using (h5.const_mul ((m : ℝ)+1)).add (h4.const_mul ((m : ℝ)*(m+1)+1))

theorem permanent_error_sqrt_log_sq_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ => Real.sqrt (permanentCapError m n/(n : ℝ))*Real.log (n : ℝ)^2)
      atTop (𝓝 0) := by
  have h := (permanent_error_log_fourth_div_tendsto_zero m).sqrt
  have he : ∀ n : ℕ, Real.sqrt (permanentCapError m n*Real.log (n : ℝ)^4/(n : ℝ)) =
      Real.sqrt (permanentCapError m n/(n : ℝ))*Real.log (n : ℝ)^2 := by
    intro n
    have ha : permanentCapError m n*Real.log (n : ℝ)^4/(n : ℝ) =
        (permanentCapError m n/(n : ℝ))*(Real.log (n : ℝ)^2)^2 := by ring
    rw [ha,Real.sqrt_mul' _ (sq_nonneg _),Real.sqrt_sq (sq_nonneg _)]
  simpa only [he,Real.sqrt_zero] using h

theorem sqrt_inverse_log_sq_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (1/(n : ℝ))*Real.log (n : ℝ)^2) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.log (n : ℝ)^4/(n : ℝ)) atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have he : ∀ n : ℕ, Real.sqrt (Real.log (n : ℝ)^4/(n : ℝ)) =
      Real.sqrt (1/(n : ℝ))*Real.log (n : ℝ)^2 := by
    intro n
    have ha : Real.log (n : ℝ)^4/(n : ℝ) = (1/(n : ℝ))*(Real.log (n : ℝ)^2)^2 := by ring
    rw [ha,Real.sqrt_mul' _ (sq_nonneg _),Real.sqrt_sq (sq_nonneg _)]
  simpa only [he,Real.sqrt_zero] using h.sqrt

end LatinonEntropy

#print axioms LatinonEntropy.permanent_error_sqrt_log_sq_tendsto_zero
#print axioms LatinonEntropy.sqrt_inverse_log_sq_tendsto_zero
