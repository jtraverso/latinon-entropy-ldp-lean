module

public import EntropyWeights
public import EntropyCorrection
public import FallbackEntropy
public import HistoryEventBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem profile_row_entropy_pointwise {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (h : LatinHistory n) (hlen : h.length = t) :
    profileLinearEntropy P t (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h) ≤
      kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos) h+(n : ℝ)+
        rowEntropyLogConstant (profileCorrectionParameters P eps heps)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
        (3*(Real.log (n : ℝ)+rowEntropyLogConstant (profileCorrectionParameters P eps heps)+1))*
          matrixMarginDefect (profileAuxiliaryCandidate P (profileProcessGood P eps heps budget) h)+
        (if historyLive (profileProcessGood P eps heps budget) h then 0 else (n : ℝ)^2*profileEntropyWeightCap P eps) := by
  let p := profileCorrectionParameters P eps heps
  let S := profileProcessPolicy P eps heps budget
  let Good := profileProcessGood P eps heps budget
  let G := rowEntropyLogConstant p
  by_cases hlive : historyLive Good h
  · simp only [Good] at hlive
    simp only [hlive,ite_true,add_zero]
    have hc : CorrectableHistory p (profileCandidate P) h := (historyLive_good Good h hlive).1
    have hr := corrected_row_entropy_target_lower P.npos p (profileCandidate P) h hc m hm hsize
    have hB := stoppedAvailability_eq_live Good (fun t i j => profileHazard P t i j) h hlive
    have hlin0 := congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => profileLinearEntropy P t Q) hB
    have hlin : profileLinearEntropy P t (stoppedAvailability Good (profileHazard P) h) =
        matrixEntropy (profileCandidate P h) := by rw [hlin0,← hlen,← profile_candidate_entropy_eq]
    have hD := congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => matrixMarginDefect Q)
      (profileAuxiliaryCandidate_eq_live P Good h hlive)
    have hentropy : kernelEntropy (S.kernel P.npos) h =
        permanentalEntropy (correctedRowMatrix P.npos p (profileCandidate P) h) := by
      rw [row_kernel_entropy_eq]
      exact congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => permanentalEntropy Q)
        (profileProcessPolicy_live P eps heps budget h hlive)
    rw [hlin,hD,hentropy]
    linarith only [hr]
  · simp only [Good] at hlive
    simp only [hlive,ite_false]
    have hlin := (profile_linear_aux_entropy_bounds P eps heps t hdegree Good h).2
    have hentropy := kernelEntropy_nonneg (S.kernel P.npos) h
    have hG : 0 ≤ G := rowEntropyLogConstant_nonneg p
    have hGB := mul_nonneg hG (Real.sqrt_nonneg (2*(n : ℝ)*permanentCapError m n))
    have hL : 0 ≤ Real.log (n : ℝ)+G+1 :=
      add_nonneg (add_nonneg (Real.log_natCast_nonneg n) hG) (by norm_num)
    have hD := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL)
      (matrixMarginDefect_nonneg (profileAuxiliaryCandidate P Good h))
    linarith only [hlin,hentropy,hGB,hD,Nat.cast_nonneg (α := ℝ) n]

theorem history_stopped_constant_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Good : List Ω → Prop) (t : ℕ) (C : ℝ) :
    historyExpectation K t (fun h => if historyLive Good h then 0 else C) =
      C*historyEventMass K t (fun h => ¬historyLive Good h) := by
  unfold historyExpectation historyEventMass
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  by_cases hl : historyLive Good h
  · simp only [hl,ite_true,not_true_eq_false,ite_false,mul_zero]
  · simp only [hl,ite_false,not_false_eq_true,ite_true]
    ring

theorem profile_row_entropy_expectation {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (t : ℕ) (hdegree : eps*n ≤ (n : ℝ)-t)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) t
      (fun h => profileLinearEntropy P t
        (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h)) ≤
      historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) t
        (kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos))+(n : ℝ)+
      rowEntropyLogConstant (profileCorrectionParameters P eps heps)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
      (3*(Real.log (n : ℝ)+rowEntropyLogConstant (profileCorrectionParameters P eps heps)+1))*
        profileExpectedDefect P eps heps budget t+
      ((n : ℝ)^2*profileEntropyWeightCap P eps)*
        historyEventMass ((profileProcessPolicy P eps heps budget).kernel P.npos) t
          (fun h => ¬historyLive (profileProcessGood P eps heps budget) h) := by
  let K := (profileProcessPolicy P eps heps budget).kernel P.npos
  let Good := profileProcessGood P eps heps budget
  have hE := historyExpectation_mono K t (fun h hh =>
    profile_row_entropy_pointwise P eps heps budget t hdegree m hm hsize h (histories_length hh))
  simp only [historyExpectation_add,historyExpectation_const,historyExpectation_mul] at hE
  rw [history_stopped_constant_expectation] at hE
  exact hE

end LatinonEntropy

#print axioms LatinonEntropy.profile_row_entropy_pointwise
#print axioms LatinonEntropy.profile_row_entropy_expectation
