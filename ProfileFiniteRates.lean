module

public import MainRangeParameters
public import ExponentialUnionRates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileSurvivalRate (a b eps : ℝ) (m n : ℕ) : ℝ :=
  (4/fixedCutDensity a b eps)*profileDriftRate (b/(a*eps)) m n+
    exponentialUnionRate 4 ((fixedCutDensity a b eps)^2/16) m n

theorem profileStabilityBound_nonneg {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (m : ℕ) : 0 ≤ profileStabilityBound P eps m := by
  have hc : 0 ≤ P.b/(P.a*eps) := div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le
  unfold profileStabilityBound
  positivity

theorem two_pow_square_exp (n : ℕ) : ((2 : ℝ)^n)^2 = Real.exp ((n : ℝ)*Real.log 4) := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 4),pow_two,← mul_pow]
  norm_num

theorem profile_finite_survival_error_le_rate {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b)
    (m T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/
        (fixedCutDensity a b eps*(n : ℝ)^2/4)+
      ((T : ℝ)*((2 : ℝ)^n)^2)*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-
        (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ)))))) ≤
      profileSurvivalRate a b eps m n := by
  let delta := fixedCutDensity a b eps
  let v := delta*(n : ℝ)^2/4
  have hdelta : 0 < delta := fixedCutDensity_pos a b eps (ha ▸ P.a_pos) heps
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hv : 0 < v := by dsimp [v]; positivity
  have htol : profileCutTolerance P eps heps = delta*(n : ℝ)^2 :=
    profile_cut_tolerance_fixed P a b eps heps ha hb
  have hT : (T : ℝ) ≤ n := Nat.cast_le.mpr (P.main_index eps heps T hdegree).le
  have hK : 0 ≤ Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (profileStabilityBound_nonneg P eps heps m))
  have hidentity := profile_normalized_drift_bound_identity P eps m
  rw [ha,hb] at hidentity
  have hbudget : (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v ≤
      (4/delta)*profileDriftRate (b/(a*eps)) m n := by
    calc
      _ ≤ (n : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hT hK) hv.le
      _ = (4/delta)*((Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/(n : ℝ)) := by
        dsimp [v]
        field_simp [hdelta.ne',hn.ne']
      _ = _ := congrArg (fun x : ℝ => (4/delta)*x) hidentity
  have hex : (n : ℝ)*(2*permanentCapError m n)-
      (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ)))) =
      2*(n : ℝ)*permanentCapError m n-(delta^2/16)*(n : ℝ)^2 := by
    rw [htol]
    field_simp [hn.ne']
    ring
  have htail : ((T : ℝ)*((2 : ℝ)^n)^2)*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-
      (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ)))))) ≤
      exponentialUnionRate 4 (delta^2/16) m n := by
    rw [hex,two_pow_square_exp]
    calc
      _ = 2*(T : ℝ)*Real.exp ((n : ℝ)*Real.log 4+
          (2*(n : ℝ)*permanentCapError m n-(delta^2/16)*(n : ℝ)^2)) := by rw [Real.exp_add]; ring
      _ ≤ 2*(n : ℝ)*Real.exp ((n : ℝ)*Real.log 4+
          (2*(n : ℝ)*permanentCapError m n-(delta^2/16)*(n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num)) (Real.exp_pos _).le
      _ = _ := by unfold exponentialUnionRate; congr 2; ring
  exact add_le_add hbudget htail

theorem profile_survival_rate_bound {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if ¬historyPastLive (profileProcessGood P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4))
          (historyPrefix h T)
      then historyWeight ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) h else 0) ≤
      profileSurvivalRate a b eps m n := by
  let delta := fixedCutDensity a b eps
  let v := delta*(n : ℝ)^2/4
  have hdelta : 0 < delta := fixedCutDensity_pos a b eps (ha ▸ P.a_pos) heps
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hv : 0 < v := by dsimp [v]; positivity
  have htol : profileCutTolerance P eps heps = delta*(n : ℝ)^2 :=
    profile_cut_tolerance_fixed P a b eps heps ha hb
  have hvsmall : v ≤ profileCutTolerance P eps heps/2 := by
    rw [htol]
    dsimp [v]
    have hpos := mul_pos hdelta (sq_pos_of_pos hn)
    linarith only [hpos]
  have hmP : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m := by
    rw [profile_upper_fixed P a b eps heps ha hb]; exact hm
  exact (profile_main_survival_bound P eps heps v hv T hdegree hvsmall m hmP hsize).trans
    (profile_finite_survival_error_le_rate P a b eps heps ha hb m T hdegree)

end LatinonEntropy

#print axioms LatinonEntropy.profile_survival_rate_bound
#print axioms LatinonEntropy.profile_finite_survival_error_le_rate
