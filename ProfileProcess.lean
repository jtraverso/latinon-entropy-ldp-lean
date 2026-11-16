module

public import ProfilePropagation
public import LatinStoppedProcess
public import HistoryExpectationTools

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileProcessGood {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) : LatinHistory n → Prop :=
  latinRowGood P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) budget

def profileProcessPolicy {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) : LatinRowPolicy n :=
  latinStoppedPolicy P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) budget

def profileAuxiliaryCandidate {n : ℕ} (P : PositiveLatinProfile n) (Good : LatinHistory n → Prop)
    (h : LatinHistory n) (i j : Fin n) : ℝ :=
  stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j

def profileExpectedDefect {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (T : ℕ) : ℝ :=
  historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T (fun h =>
    matrixMarginDefect (profileAuxiliaryCandidate P (profileProcessGood P eps heps budget) h))

def profileActualDriftCost {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (h : LatinHistory n) : ℝ :=
  if historyLive (profileProcessGood P eps heps budget) h then
    ∑ i, ∑ j, |permanentMarginal ((profileProcessPolicy P eps heps budget).matrix h) i j-
      profileCandidate P h i j|
  else 0

theorem matrixMarginDefect_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ matrixMarginDefect M :=
  add_nonneg (sum_nonneg (fun _ _ => abs_nonneg _)) (sum_nonneg (fun _ _ => abs_nonneg _))

theorem profileAuxiliaryCandidate_eq_live {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (hlive : historyLive Good h) :
    profileAuxiliaryCandidate P Good h = profileCandidate P h := by
  funext i j
  have he := congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => Q i j)
    (stoppedAvailability_eq_live Good (profileHazard P) h hlive)
  change stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j = _
  rw [he]
  rfl

theorem profileProcessPolicy_live {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (h : LatinHistory n) (hlive : historyLive (profileProcessGood P eps heps budget) h) :
    (profileProcessPolicy P eps heps budget).matrix h =
      (correctedRowPolicy P.npos (profileCorrectionParameters P eps heps) (profileCandidate P)).matrix h :=
  stoppedRowPolicy_live P.npos (correctedRowPolicy P.npos (profileCorrectionParameters P eps heps)
    (profileCandidate P)) (profileProcessGood P eps heps budget) h hlive

theorem profile_live_drift_bound {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (h : LatinHistory n) (hlive : historyLive (profileProcessGood P eps heps budget) h)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    (∑ i, ∑ j, |permanentMarginal ((profileProcessPolicy P eps heps budget).matrix h) i j-
      profileCandidate P h i j|) ≤ Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
        3*matrixMarginDefect (profileAuxiliaryCandidate P (profileProcessGood P eps heps budget) h) := by
  have hc : CorrectableHistory (profileCorrectionParameters P eps heps) (profileCandidate P) h :=
    (historyLive_good (profileProcessGood P eps heps budget) h hlive).1
  rw [profileProcessPolicy_live P eps heps budget h hlive,
    profileAuxiliaryCandidate_eq_live P (profileProcessGood P eps heps budget) h hlive]
  exact proposedRowDrift_le P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) h hc m hm hsize

theorem profileActualDriftCost_nonneg {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (h : LatinHistory n) : 0 ≤ profileActualDriftCost P eps heps budget h := by
  unfold profileActualDriftCost
  split_ifs
  · exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => abs_nonneg _))
  · exact le_rfl

theorem profileActualDriftCost_bound {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (h : LatinHistory n) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    profileActualDriftCost P eps heps budget h ≤ Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
      3*matrixMarginDefect (profileAuxiliaryCandidate P (profileProcessGood P eps heps budget) h) := by
  by_cases hlive : historyLive (profileProcessGood P eps heps budget) h
  · simpa only [profileActualDriftCost,hlive,ite_true] using profile_live_drift_bound P eps heps budget h hlive m hm hsize
  · simp only [profileActualDriftCost,hlive,ite_false]
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (matrixMarginDefect_nonneg _))

theorem expected_profile_drift_le {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
      (profileActualDriftCost P eps heps budget) ≤
      Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileExpectedDefect P eps heps budget T := by
  calc
    _ ≤ historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T (fun h =>
        Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*
          matrixMarginDefect (profileAuxiliaryCandidate P (profileProcessGood P eps heps budget) h)) :=
      historyExpectation_mono _ _ (fun h _ => profileActualDriftCost_bound P eps heps budget h m hm hsize)
    _ = _ := by
      simp only [historyExpectation_add,historyExpectation_const,historyExpectation_mul,profileExpectedDefect]

theorem profile_cost_matches_stopped_proposal {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (h : LatinHistory n) :
    profileActualDriftCost P eps heps budget h =
      if historyLive (profileProcessGood P eps heps budget) h then
        proposedRowDrift P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) h else 0 := by
  by_cases hlive : historyLive (profileProcessGood P eps heps budget) h
  · simp only [profileActualDriftCost,hlive,ite_true]
    rw [profileProcessPolicy_live P eps heps budget h hlive]
    rfl
  · simp only [profileActualDriftCost,hlive,ite_false]

theorem expected_profile_budget_le {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
      (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget h)) ≤
      (T : ℝ)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
        3*(∑ t ∈ range T, profileExpectedDefect P eps heps budget t) := by
  rw [history_predictable_sum]
  calc
    _ ≤ ∑ t ∈ range T, (Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
        3*profileExpectedDefect P eps heps budget t) :=
      sum_le_sum (fun t _ => expected_profile_drift_le P eps heps budget m hm hsize t)
    _ = _ := by simp only [sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul]

theorem profile_budget_markov {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (heps : 0 < eps)
    (budget : ℝ) (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (v : ℝ) (hv : 0 < v) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) T,
      if v ≤ pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      ((T : ℝ)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
        3*(∑ t ∈ range T, profileExpectedDefect P eps heps budget t))/v := by
  have hnonneg : ∀ h : LatinHistory n,
      0 ≤ pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
    intro h
    induction h with
    | nil => exact le_rfl
    | cons sigma h ih => exact add_nonneg ih (profileActualDriftCost_nonneg P eps heps budget h)
  exact (history_markov ((profileProcessPolicy P eps heps budget).kernel P.npos) T _
    (fun h _ => hnonneg h) v hv).trans
      (div_le_div_of_nonneg_right (expected_profile_budget_le P eps heps budget m hm hsize T) hv.le)

end LatinonEntropy

#print axioms LatinonEntropy.profileActualDriftCost_bound
#print axioms LatinonEntropy.expected_profile_budget_le
#print axioms LatinonEntropy.profile_budget_markov
