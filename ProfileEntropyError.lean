module

public import ProfileFiniteRates
public import RowLogBands
public import EntropyWeights

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem profile_survival_rate_nonneg (a b eps : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (heps : 0 < eps) (m n : ℕ) : 0 ≤ profileSurvivalRate a b eps m n := by
  have hd := (fixedCutDensity_pos a b eps ha heps).le
  have hc : 0 ≤ b/(a*eps) := div_nonneg hb (mul_pos ha heps).le
  unfold profileSurvivalRate profileDriftRate exponentialUnionRate
  positivity

def profileRowEntropyError {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (m : ℕ) : ℝ :=
  rowEntropyLogConstant (profileCorrectionParameters P eps heps)*
      Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
    3*(Real.log (n : ℝ)+rowEntropyLogConstant (profileCorrectionParameters P eps heps)+1)*
      profileStabilityBound P eps m+
    profileEntropyWeightCap P eps*((n : ℝ)*
      (Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m))+
    ((n : ℝ)^2*profileEntropyWeightCap P eps)*profileSurvivalRate a b eps m n

theorem profileRowEntropyError_nonneg {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b) (m : ℕ) :
    0 ≤ profileRowEntropyError P a b eps heps m := by
  have hG := rowEntropyLogConstant_nonneg (profileCorrectionParameters P eps heps)
  have hlog := Real.log_natCast_nonneg n
  have hD := profileStabilityBound_nonneg P eps heps m
  have hW := profileEntropyWeightCap_nonneg P eps heps
  have hR := profile_survival_rate_nonneg a b eps (ha ▸ P.a_pos)
    (hb ▸ P.a_pos.le.trans P.a_le_b) heps m n
  unfold profileRowEntropyError
  positivity

end LatinonEntropy

#print axioms LatinonEntropy.profileRowEntropyError_nonneg
