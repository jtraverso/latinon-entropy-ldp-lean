module

public import PermanentAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology

def exponentialUnionRate (q k : ℝ) (m n : ℕ) : ℝ :=
  2*(n : ℝ)*Real.exp ((n : ℝ)*Real.log q+2*(n : ℝ)*permanentCapError m n-k*(n : ℝ)^2)

theorem exponentialUnionRate_nonneg (q k : ℝ) (m n : ℕ) :
    0 ≤ exponentialUnionRate q k m n := by unfold exponentialUnionRate; positivity

theorem normalized_union_exponent_tendsto_zero (q : ℝ) (m : ℕ) :
    Tendsto (fun n : ℕ => (2*permanentCapError m n+Real.log q+1)/(n : ℝ)) atTop (𝓝 0) := by
  have h1 := (permanentCapError_div_tendsto_zero m).const_mul 2
  have h2 := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (Real.log q+1)
  have he : (fun n : ℕ => (2*permanentCapError m n+Real.log q+1)/(n : ℝ)) =
      (fun n : ℕ => 2*(permanentCapError m n/(n : ℝ))+(Real.log q+1)*(n : ℝ)⁻¹) := by
    funext n; ring
  rw [he]
  simpa using h1.add h2

theorem eventually_exponentialUnionRate_le (q k : ℝ) (hk : 0 < k) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, exponentialUnionRate q k m n ≤ 2*(n : ℝ)*Real.exp (-(n : ℝ)) := by
  have hsmall := (tendsto_order.mp (normalized_union_exponent_tendsto_zero q m)).2 k hk
  filter_upwards [hsmall,eventually_ge_atTop 1] with n hs hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := (div_lt_iff₀ hnR).mp hs
  have hmul := mul_le_mul_of_nonneg_right hd.le hnR.le
  have hex : (n : ℝ)*Real.log q+2*(n : ℝ)*permanentCapError m n-k*(n : ℝ)^2 ≤ -(n : ℝ) := by
    nlinarith only [hmul]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (by positivity)

theorem exponential_union_rate_log_sq_tendsto_zero (q k : ℝ) (hk : 0 < k) (m : ℕ) :
    Tendsto (fun n : ℕ => exponentialUnionRate q k m n*Real.log (n : ℝ)^2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 2*((n : ℝ)^3*Real.exp (-(n : ℝ)))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      tendsto_natCast_atTop_atTop).const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg
    (exponentialUnionRate_nonneg q k m n) (sq_nonneg _))) ?_ hlim
  filter_upwards [eventually_exponentialUnionRate_le q k hk m,eventually_ge_atTop 1] with n hb hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 := Real.log_natCast_nonneg n
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
  have hsq : Real.log (n : ℝ)^2 ≤ (n : ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlog) (add_nonneg hnR.le hlog0)]
  calc
    _ ≤ (2*(n : ℝ)*Real.exp (-(n : ℝ)))*(n : ℝ)^2 :=
      mul_le_mul hb hsq (sq_nonneg _) (by positivity)
    _ = _ := by ring

end LatinonEntropy

#print axioms LatinonEntropy.exponential_union_rate_log_sq_tendsto_zero
