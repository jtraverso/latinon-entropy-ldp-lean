module

public import LatinRowPolicy
public import StoppedAvailability
public import HistoryMartingale
public import PermanentalRecentering
public import FiniteChernoff

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def stoppedRowPolicy {n : ℕ} (hn : 0 < n) (P : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) : LatinRowPolicy n where
  matrix h i j := if historyLive Good h then P.matrix h i j else fallbackRowMatrix n h i j
  nonneg := by intro h i j; split_ifs; exact P.nonneg h i j; exact fallbackRowMatrix_nonneg h i j
  row := by
    intro h i
    by_cases hlive : historyLive Good h
    · simpa only [hlive,ite_true] using P.row h i
    · simpa only [hlive,ite_false] using fallbackRowMatrix_row hn h i
  col := by
    intro h j
    by_cases hlive : historyLive Good h
    · simpa only [hlive,ite_true] using P.col h j
    · simpa only [hlive,ite_false] using fallbackRowMatrix_col hn h j
  support := by
    intro h hv ht i j hz
    by_cases hlive : historyLive Good h
    · simpa only [hlive,ite_true] using P.support h hv ht i j hz
    · simpa only [hlive,ite_false,fallbackRowPolicy] using (fallbackRowPolicy n hn).support h hv ht i j hz

theorem stoppedRowPolicy_live {n : ℕ} (hn : 0 < n) (P : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (hlive : historyLive Good h) :
    (stoppedRowPolicy hn P Good).matrix h = P.matrix h := by
  funext i j
  simp only [stoppedRowPolicy,hlive,ite_true]

theorem stoppedRowPolicy_fallback {n : ℕ} (hn : 0 < n) (P : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (hstop : ¬historyLive Good h) :
    (stoppedRowPolicy hn P Good).matrix h = fallbackRowMatrix n h := by
  funext i j
  simp only [stoppedRowPolicy,hstop,ite_false]

def killedPermanentalStatistic {n : ℕ} (P : LatinRowPolicy n) (Good : LatinHistory n → Prop)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (h : LatinHistory n)
    (sigma : Equiv.Perm (Fin n)) : ℝ :=
  if historyLive Good h then permutationStatistic (g h) sigma-
    matrixPairing (permanentMarginal (P.matrix h)) (g h) else 0

theorem killedPermanentalStatistic_mean_zero {n : ℕ} (hn : 0 < n)
    (P : LatinRowPolicy n) (Good : LatinHistory n → Prop)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (h : LatinHistory n) :
    (∑ sigma, (P.kernel hn).transition h sigma*killedPermanentalStatistic P Good g h sigma) = 0 := by
  by_cases hlive : historyLive Good h
  · change (∑ sigma, permanentLaw (P.matrix h) sigma*killedPermanentalStatistic P Good g h sigma) = 0
    simp only [killedPermanentalStatistic,hlive,ite_true,mul_sub,sum_sub_distrib,← sum_mul,
      sum_permanentLaw _ (P.permanent_pos hn h).ne',one_mul]
    rw [← permanentMarginal_pairing]
    unfold matrixPairing
    ring
  · simp only [killedPermanentalStatistic,hlive,ite_false,mul_zero,sum_const_zero]

theorem killedPermanentalStatistic_mgf_le {n : ℕ} (hn : 0 < n) (m : ℕ) (c : ℝ)
    (P : LatinRowPolicy n) (Good : LatinHistory n → Prop)
    (hcap : ∀ h, historyLive Good h → ∀ i j, P.matrix h i j ≤ c/n)
    (hm : Real.exp 2*c ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (hg : ∀ h i j, |g h i j| ≤ 1)
    (lambda : ℝ) (hlambda : |lambda| ≤ 1) (h : LatinHistory n) :
    (∑ sigma, (P.kernel hn).transition h sigma*
      Real.exp (lambda*killedPermanentalStatistic P Good g h sigma)) ≤
      Real.exp ((n : ℝ)*lambda^2+2*permanentCapError m n) := by
  by_cases hlive : historyLive Good h
  · have hlog := permanental_recentered_log_mgf_le hn m c (P.matrix h)
      (P.nonneg h) (P.row h) (P.col h) (hcap h hlive) hm hsize (g h) (hg h) lambda hlambda
    have hpos := finite_exponential_sum_pos (permanentLaw (P.matrix h))
      (fun sigma => lambda*(permutationStatistic (g h) sigma-
        matrixPairing (permanentMarginal (P.matrix h)) (g h)))
      (permanentLaw_nonneg _ (P.nonneg h) (P.permanent_pos hn h))
      (sum_permanentLaw _ (P.permanent_pos hn h).ne')
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at h
    simpa only [LatinRowPolicy.kernel,killedPermanentalStatistic,hlive,ite_true] using h
  · simp only [killedPermanentalStatistic,hlive,ite_false,mul_zero,Real.exp_zero,mul_one,
      (P.kernel hn).total]
    apply Real.one_le_exp_iff.mpr
    have hd := permanentCapError_nonneg n m hn
    positivity

theorem killed_history_mgf_le {n : ℕ} (hn : 0 < n) (m : ℕ) (c : ℝ)
    (P : LatinRowPolicy n) (Good : LatinHistory n → Prop)
    (hcap : ∀ h, historyLive Good h → ∀ i j, P.matrix h i j ≤ c/n)
    (hm : Real.exp 2*c ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (hg : ∀ h i j, |g h i j| ≤ 1)
    (lambda : ℝ) (hlambda : |lambda| ≤ 1) (T : ℕ) :
    historyExpectation (P.kernel hn) T (fun h =>
      Real.exp (lambda*pathSum (killedPermanentalStatistic P Good g) h)) ≤
      Real.exp ((T : ℝ)*((n : ℝ)*lambda^2+2*permanentCapError m n)) := by
  have h := history_mgf_le (P.kernel hn) (killedPermanentalStatistic P Good g)
    (fun _ => (n : ℝ)*lambda^2+2*permanentCapError m n) lambda
    (killedPermanentalStatistic_mgf_le hn m c P Good hcap hm hsize g hg lambda hlambda) T
  simpa [mul_add] using h

theorem killed_history_mean_zero {n : ℕ} (hn : 0 < n) (P : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (g : LatinHistory n → Fin n → Fin n → ℝ) (T : ℕ) :
    historyExpectation (P.kernel hn) T (pathSum (killedPermanentalStatistic P Good g)) = 0 :=
  history_pathSum_mean_zero _ _ (killedPermanentalStatistic_mean_zero hn P Good g) T

end LatinonEntropy

#print axioms LatinonEntropy.stoppedRowPolicy
#print axioms LatinonEntropy.killed_history_mgf_le
#print axioms LatinonEntropy.killed_history_mean_zero
