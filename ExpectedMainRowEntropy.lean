module

public import MainRowEntropy
public import ExpectedFluidEntropy
public import HistoryPrefixLaw

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- One main row of the actual law, with all three error sources derived:
marginals/correction, expected fluid drift, and stopped-history mass. -/
theorem expected_main_row_entropy_lower {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (t : ℕ) (ht : t < T) :
    profileFluidRowEntropy P t-(n : ℝ)-
      rowEntropyLogConstant (profileCorrectionParameters P eps heps)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)-
      (3*(Real.log (n : ℝ)+rowEntropyLogConstant (profileCorrectionParameters P eps heps)+1))*profileStabilityBound P eps m-
      profileEntropyWeightCap P eps*((t : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m))-
      ((n : ℝ)^2*profileEntropyWeightCap P eps)*profileSurvivalRate a b eps m n ≤
      historyExpectation
        ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) t
        (kernelEntropy ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos)) := by
  let v := fixedCutDensity a b eps*(n : ℝ)^2/4
  have hmP : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m := by
    rw [profile_upper_fixed P a b eps heps ha hb]; exact hm
  have htR : (t : ℝ) ≤ T := Nat.cast_le.mpr ht.le
  have hdeg : eps*n ≤ (n : ℝ)-t := by linarith only [hdegree,htR]
  have hrow := profile_row_entropy_expectation P eps heps v t hdeg m hmP hsize
  have hfluid := profile_aux_entropy_expectation_lower P eps heps v t hdeg m hmP hsize
  have hdefect := profile_expected_defect_uniform P eps heps v m hmP hsize T hdegree t ht.le
  have hstop := profile_notLive_mass_le_rate P a b eps heps ha hb m hm hsize T hdegree t ht
  have hG := rowEntropyLogConstant_nonneg (profileCorrectionParameters P eps heps)
  have hL : 0 ≤ 3*(Real.log (n : ℝ)+rowEntropyLogConstant (profileCorrectionParameters P eps heps)+1) :=
    mul_nonneg (by norm_num) (add_nonneg (add_nonneg (Real.log_natCast_nonneg n) hG) (by norm_num))
  have hdefectMul := mul_le_mul_of_nonneg_left hdefect hL
  have hstopMul := mul_le_mul_of_nonneg_left hstop
    (mul_nonneg (sq_nonneg (n : ℝ)) (profileEntropyWeightCap_nonneg P eps heps))
  linarith only [hrow,hfluid,hdefectMul,hstopMul]

end LatinonEntropy

#print axioms LatinonEntropy.expected_main_row_entropy_lower
