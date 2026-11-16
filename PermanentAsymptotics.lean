module

public import PermanentCapScalar

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

theorem permanentCapError_div_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ => permanentCapError m n / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he : (fun n : ℕ => permanentCapError m n / (n : ℝ)) =
      (fun n : ℕ => ((m : ℝ)+1)*(Real.log (n : ℝ)/(n : ℝ)) +
        ((m : ℝ)*(m+1)+1)*(n : ℝ)⁻¹) := by
    funext n
    unfold permanentCapError
    ring
  rw [he]
  simpa using (hlog.const_mul ((m : ℝ)+1)).add
    (hinv.const_mul ((m : ℝ)*(m+1)+1))

theorem eventually_permanentCapError_le_half (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, permanentCapError m n ≤ (n : ℝ)/2 := by
  have hsmall : ∀ᶠ n : ℕ in atTop, permanentCapError m n/(n : ℝ) < (1 : ℝ)/2 :=
    (tendsto_order.mp (permanentCapError_div_tendsto_zero m)).2 _ (by norm_num)
  filter_upwards [hsmall,eventually_ge_atTop 1] with n hsmall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (div_lt_iff₀ hnR).mp hsmall
  linarith

end LatinonEntropy

#print axioms LatinonEntropy.eventually_permanentCapError_le_half
