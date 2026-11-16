module

public import HistoryPrefixes
public import ProfileDefectStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Evaluate the budget of the main range on the full history law, without
charging any increment in the deliberately uncontrolled tail. -/
theorem history_truncated_cost_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (F : List Ω → ℝ) (T N : ℕ) (hTN : T ≤ N) :
    historyExpectation K N (pathSum (truncateIncrement T (fun h (_ : Ω) => F h))) =
      historyExpectation K T (pathSum (fun h (_ : Ω) => F h)) := by
  change historyExpectation K N (pathSum (fun h (_ : Ω) => if h.length < T then F h else 0)) = _
  rw [history_predictable_sum,history_predictable_sum]
  have he : ∀ s, historyExpectation K s (fun h => if h.length < T then F h else 0) =
      if s < T then historyExpectation K s F else 0 := by
    intro s
    by_cases hs : s < T
    · simp only [hs,ite_true]
      apply historyExpectation_congr_positive
      intro h hh _
      simp only [histories_length hh,hs,ite_true]
    · simp only [hs,ite_false]
      calc
        _ = historyExpectation K s (fun _ => 0) := by
          apply historyExpectation_congr_positive
          intro h hh _
          simp only [histories_length hh,hs,ite_false]
        _ = 0 := historyExpectation_const K s 0
  simp_rw [he]
  calc
    _ = ∑ s ∈ range T, if s < T then historyExpectation K s F else 0 := by
      symm
      apply sum_subset (range_mono hTN)
      intro s _ hs
      simp only [mem_range] at hs
      simp only [hs,ite_false]
    _ = _ := sum_congr rfl (fun s hs => by simp only [mem_range.mp hs,ite_true])

theorem expected_profile_truncated_budget {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T N : ℕ) (hTN : T ≤ N)
    (hdegree : eps*n ≤ (n : ℝ)-T) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) N
      (pathSum (truncateIncrement T (fun h (_ : Equiv.Perm (Fin n)) =>
        profileActualDriftCost P eps heps budget h))) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m) := by
  rw [history_truncated_cost_expectation _ _ T N hTN]
  exact expected_profile_budget_uniform P eps heps budget m hm hsize T hdegree

theorem profile_full_history_budget_markov {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T N : ℕ) (hTN : T ≤ N)
    (hdegree : eps*n ≤ (n : ℝ)-T) (v : ℝ) (hv : 0 < v) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) N,
      if v ≤ pathSum (truncateIncrement T (fun g (_ : Equiv.Perm (Fin n)) =>
          profileActualDriftCost P eps heps budget g)) h
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v := by
  have hnonneg : ∀ h : LatinHistory n,
      0 ≤ pathSum (truncateIncrement T (fun g (_ : Equiv.Perm (Fin n)) =>
        profileActualDriftCost P eps heps budget g)) h := by
    intro h
    induction h with
    | nil => exact le_rfl
    | cons a h ih =>
      apply add_nonneg ih
      unfold truncateIncrement
      split_ifs
      · exact profileActualDriftCost_nonneg P eps heps budget h
      · exact le_rfl
  exact (history_markov _ N _ (fun h _ => hnonneg h) v hv).trans
    (div_le_div_of_nonneg_right
      (expected_profile_truncated_budget P eps heps budget m hm hsize T N hTN hdegree) hv.le)

end LatinonEntropy

#print axioms LatinonEntropy.history_truncated_cost_expectation
#print axioms LatinonEntropy.profile_full_history_budget_markov
