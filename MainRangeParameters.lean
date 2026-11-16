module

public import ProfileSurvivalProbability
public import ProfileBudgetRates
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

noncomputable section

namespace LatinonEntropy

def fixedCorrectionUpper (a b eps : ℝ) : ℝ :=
  max (max a (b/(a*eps))) (16/(min 1 (a*eps/2)*eps))

def fixedCutDensity (a b eps : ℝ) : ℝ :=
  min 1 (a*eps/2)*eps/(64*fixedCorrectionUpper a b eps)

theorem fixedCorrectionUpper_pos (a b eps : ℝ) (ha : 0 < a) : 0 < fixedCorrectionUpper a b eps :=
  (ha.trans_le (le_max_left _ _)).trans_le (le_max_left _ _)

theorem fixedCutDensity_pos (a b eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    0 < fixedCutDensity a b eps := by
  unfold fixedCutDensity
  exact div_pos (mul_pos (lt_min (by norm_num) (half_pos (mul_pos ha heps))) heps)
    (mul_pos (by norm_num) (fixedCorrectionUpper_pos a b eps ha))

theorem profile_upper_fixed {n : ℕ} (P : PositiveLatinProfile n) (a b eps : ℝ) (heps : 0 < eps)
    (ha : P.a = a) (hb : P.b = b) :
    (profileCorrectionParameters P eps heps).upper = fixedCorrectionUpper a b eps := by
  simp only [profileCorrectionParameters,RowCorrectionParameters.upper,fixedCorrectionUpper,ha,hb]

theorem profile_cut_tolerance_fixed {n : ℕ} (P : PositiveLatinProfile n) (a b eps : ℝ) (heps : 0 < eps)
    (ha : P.a = a) (hb : P.b = b) :
    profileCutTolerance P eps heps = fixedCutDensity a b eps*(n : ℝ)^2 := by
  unfold profileCutTolerance
  rw [profile_upper_fixed P a b eps heps ha hb]
  simp only [profileCorrectionParameters,ha,fixedCutDensity]
  ring

def mainRange (eps : ℝ) (n : ℕ) : ℕ := ⌊(1-eps)*(n : ℝ)⌋₊

theorem mainRange_degree (eps : ℝ) (heps1 : eps ≤ 1) (n : ℕ) :
    eps*n ≤ (n : ℝ)-mainRange eps n := by
  have hnonneg : 0 ≤ (1-eps)*(n : ℝ) := mul_nonneg (sub_nonneg.mpr heps1) (Nat.cast_nonneg n)
  have hf := Nat.floor_le hnonneg
  change eps*n ≤ (n : ℝ)-⌊(1-eps)*(n : ℝ)⌋₊
  linarith only [hf]

theorem mainRange_tail (eps : ℝ) (n : ℕ) :
    (n : ℝ)-mainRange eps n < eps*n+1 := by
  have hf := Nat.lt_floor_add_one ((1-eps)*(n : ℝ))
  change (n : ℝ)-⌊(1-eps)*(n : ℝ)⌋₊ < eps*n+1
  linarith only [hf]

theorem fixed_permanent_cap_index_exists (a b eps : ℝ) :
    ∃ m : ℕ, Real.exp 2*fixedCorrectionUpper a b eps ≤ m :=
  ⟨⌈Real.exp 2*fixedCorrectionUpper a b eps⌉₊,Nat.le_ceil _⟩

end LatinonEntropy

#print axioms LatinonEntropy.profile_cut_tolerance_fixed
#print axioms LatinonEntropy.mainRange_degree
#print axioms LatinonEntropy.mainRange_tail
