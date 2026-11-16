module

public import MainRangeParameters

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem fixedCutDensity_le_eps_sq (a b eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    fixedCutDensity a b eps ≤ eps^2/1024 := by
  let rho := min 1 (a*eps/2)
  let C := fixedCorrectionUpper a b eps
  have hr : 0 < rho := lt_min (by norm_num) (half_pos (mul_pos ha heps))
  have hr1 : rho ≤ 1 := min_le_left _ _
  have hC : 0 < C := fixedCorrectionUpper_pos a b eps ha
  have hprod : 16 ≤ C*(rho*eps) := (div_le_iff₀ (mul_pos hr heps)).mp (le_max_right _ _)
  have hCe : 16 ≤ C*eps := by
    calc
      _ ≤ C*(rho*eps) := hprod
      _ = rho*(C*eps) := by ring
      _ ≤ 1*(C*eps) := mul_le_mul_of_nonneg_right hr1 (mul_pos hC heps).le
      _ = _ := one_mul _
  have h16r : 16*rho ≤ C*eps := by linarith only [hr1,hCe]
  have hs := mul_le_mul_of_nonneg_right h16r heps.le
  change rho*eps/(64*C) ≤ eps^2/1024
  apply (div_le_iff₀ (mul_pos (by norm_num) hC)).mpr
  nlinarith only [hs]

theorem fixedCutDensity_le_eps (a b eps : ℝ) (ha : 0 < a) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    fixedCutDensity a b eps ≤ eps/1024 := by
  have hd := fixedCutDensity_le_eps_sq a b eps ha heps
  have hs : eps^2 ≤ eps := by nlinarith only [mul_nonneg heps.le (sub_nonneg.mpr heps1)]
  linarith only [hd,hs]

theorem main_range_full_error_le_four_eps (a b eps : ℝ) (ha : 0 < a)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (n : ℕ) (hn : 2 ≤ eps*(n : ℝ)) :
    2*(eps*(n : ℝ)^2/8)+2*(fixedCutDensity a b eps*(n : ℝ)^2/4)+
      2*(n : ℝ)*((n : ℝ)-mainRange eps n) ≤ 4*eps*(n : ℝ)^2 := by
  have hd := mul_le_mul_of_nonneg_right (fixedCutDensity_le_eps a b eps ha heps heps1) (sq_nonneg (n : ℝ))
  have ht := mul_le_mul_of_nonneg_left (mainRange_tail eps n).le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n))
  have hlarge := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg n)
  have hnn := mul_nonneg heps.le (sq_nonneg (n : ℝ))
  nlinarith only [hd,ht,hlarge,hnn]

end LatinonEntropy

#print axioms LatinonEntropy.main_range_full_error_le_four_eps
