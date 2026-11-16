module

public import CorrectedRowPolicy
public import HistoryTails
public import StoppedBudget

@[expose] public section

/-! A concrete stopped row process: correction whenever the current guard
and the past drift budget pass, permanent sampling, and regular fallback
after the first failure. Its local concentration bound is derived from C1
and C2, rather than supplied as a hypothesis. -/

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def proposedRowDrift {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n) : ℝ :=
  ∑ i, ∑ j, |permanentMarginal ((correctedRowPolicy hn p M).matrix h) i j-M h i j|

def proposedDriftBudget {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n) : ℝ :=
  pathSum (fun g (_ : Equiv.Perm (Fin n)) => proposedRowDrift hn p M g) h

def latinRowGood {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (h : LatinHistory n) : Prop :=
  budgetedGood (CorrectableHistory p M) (proposedRowDrift hn p M) budget h

def latinStoppedPolicy {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) : LatinRowPolicy n :=
  stoppedRowPolicy hn (correctedRowPolicy hn p M) (latinRowGood hn p M budget)

def matrixMarginDefect {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i, |(∑ j, Q i j)-1|)+∑ j, |(∑ i, Q i j)-1|

theorem proposedRowDrift_le {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hc : CorrectableHistory p M h) (m : ℕ)
    (hm : Real.exp 2*p.upper ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    proposedRowDrift hn p M h ≤ Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*matrixMarginDefect (M h) := by
  let Q := correctedRowMatrix hn p M h
  have hs : RowCorrectionOutput p M h Q := correctedRowMatrix_spec hn p M h hc
  have hcap : ∀ i j, Q i j ≤ p.upper/n := correctedRowPolicy_cap hn p M h hc
  have hlocal := permanental_marginal_l1_le hn m p.upper Q hs.2.2.1 hs.1 hs.2.1 hcap hm hsize
  have hcost : (∑ i, ∑ j, |Q i j-M h i j|) ≤ 3*matrixMarginDefect (M h) := hs.2.2.2.2.2
  change (∑ i, ∑ j, |permanentMarginal Q i j-M h i j|) ≤ _
  calc
    _ ≤ ∑ i, ∑ j, (|permanentMarginal Q i j-Q i j|+|Q i j-M h i j|) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => abs_sub_le _ _ _))
    _ = (∑ i, ∑ j, |permanentMarginal Q i j-Q i j|)+(∑ i, ∑ j, |Q i j-M h i j|) := by
      simp only [sum_add_distrib]
    _ ≤ _ := add_le_add hlocal hcost

theorem latinStoppedPolicy_live_cap {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (h : LatinHistory n)
    (hlive : historyLive (latinRowGood hn p M budget) h) (i j : Fin n) :
    (latinStoppedPolicy hn p M budget).matrix h i j ≤ p.upper/n := by
  have hc := (historyLive_good (latinRowGood hn p M budget) h hlive).1
  simpa only [latinStoppedPolicy,stoppedRowPolicy,hlive,ite_true] using correctedRowPolicy_cap hn p M h hc i j

theorem latinStoppedPolicy_fallback {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (h : LatinHistory n)
    (hstop : ¬historyLive (latinRowGood hn p M budget) h) :
    (latinStoppedPolicy hn p M budget).matrix h = fallbackRowMatrix n h :=
  stoppedRowPolicy_fallback hn (correctedRowPolicy hn p M) (latinRowGood hn p M budget) h hstop

theorem latinStoppedProcess_valid {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) :
    (∑ h ∈ (histories (Equiv.Perm (Fin n)) n).filter LatinHistoryValid,
      historyWeight ((latinStoppedPolicy hn p M budget).kernel hn) h) = 1 :=
  (latinStoppedPolicy hn p M budget).probability_valid_histories hn n le_rfl

theorem latinStoppedProcess_mgf_le {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*p.upper ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (hg : ∀ h i j, |g h i j| ≤ 1)
    (lambda : ℝ) (hlambda : |lambda| ≤ 1) (T : ℕ) :
    historyExpectation ((latinStoppedPolicy hn p M budget).kernel hn) T (fun h =>
      Real.exp (lambda*pathSum (killedPermanentalStatistic (latinStoppedPolicy hn p M budget)
        (latinRowGood hn p M budget) g) h)) ≤
      Real.exp ((T : ℝ)*((n : ℝ)*lambda^2+2*permanentCapError m n)) :=
  killed_history_mgf_le hn m p.upper (latinStoppedPolicy hn p M budget) (latinRowGood hn p M budget)
    (latinStoppedPolicy_live_cap hn p M budget) hm hsize g hg lambda hlambda T

theorem latinStoppedProcess_deviation_le {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*p.upper ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (hg : ∀ h i j, |g h i j| ≤ 1)
    (T : ℕ) (hT : 0 < T) (u : ℝ) (hu0 : 0 ≤ u) (huT : u ≤ (T : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) T,
      if u ≤ |pathSum (killedPermanentalStatistic (latinStoppedPolicy hn p M budget)
        (latinRowGood hn p M budget) g) h|
      then historyWeight ((latinStoppedPolicy hn p M budget).kernel hn) h else 0) ≤
      2*Real.exp ((T : ℝ)*(2*permanentCapError m n)-u^2/(2*((T : ℝ)*(2*(n : ℝ))))) :=
  killed_history_deviation_le hn m p.upper (latinStoppedPolicy hn p M budget) (latinRowGood hn p M budget)
    (latinStoppedPolicy_live_cap hn p M budget) hm hsize g hg T hT u hu0 huT

theorem latinStopped_first_failure {n : ℕ} (hn : 0 < n) (p : RowCorrectionParameters)
    (M : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (budget : ℝ) (h : LatinHistory n)
    (hpast : historyPastLive (latinRowGood hn p M budget) h)
    (hstop : ¬historyLive (latinRowGood hn p M budget) h) :
    ¬CorrectableHistory p M h ∨ budget < pathSum (fun g (_ : Equiv.Perm (Fin n)) =>
      if historyLive (latinRowGood hn p M budget) g then proposedRowDrift hn p M g else 0) h :=
  budgeted_first_failure (CorrectableHistory p M) (proposedRowDrift hn p M) budget h hpast hstop

end LatinonEntropy

#print axioms LatinonEntropy.latinStoppedProcess_valid
#print axioms LatinonEntropy.latinStoppedProcess_mgf_le
#print axioms LatinonEntropy.latinStoppedProcess_deviation_le
#print axioms LatinonEntropy.latinStopped_first_failure
#print axioms LatinonEntropy.proposedRowDrift_le
