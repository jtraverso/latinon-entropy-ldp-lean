module

public import HistoryMartingale

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem historyExpectation_congr_positive {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (F G : List Ω → ℝ)
    (heq : ∀ h ∈ histories Ω T, 0 < historyWeight K h → F h = G h) :
    historyExpectation K T F = historyExpectation K T G := by
  apply sum_congr rfl
  intro h hh
  by_cases hw : historyWeight K h = 0
  · simp only [hw,zero_mul]
  · rw [heq h hh (lt_of_le_of_ne (historyWeight_nonneg K h) (Ne.symm hw))]

theorem historyExpectation_sum {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset I) (F : I → List Ω → ℝ) :
    historyExpectation K T (fun h => ∑ i ∈ S, F i h) =
      ∑ i ∈ S, historyExpectation K T (F i) := by
  unfold historyExpectation
  simp only [mul_sum]
  rw [sum_comm]

theorem historyExpectation_nonneg {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (F : List Ω → ℝ) (hF : ∀ h ∈ histories Ω T, 0 ≤ F h) :
    0 ≤ historyExpectation K T F :=
  sum_nonneg (fun h hh => mul_nonneg (historyWeight_nonneg K h) (hF h hh))

theorem history_predictable_sum {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (F : List Ω → ℝ) (T : ℕ) :
    historyExpectation K T (pathSum (fun h (_ : Ω) => F h)) =
      ∑ t ∈ range T, historyExpectation K t F := by
  induction T with
  | zero => simp [historyExpectation,histories,pathSum]
  | succ T ih =>
    rw [historyExpectation_tower]
    have he : ∀ h, (∑ a, K.transition h a*pathSum (fun h (_ : Ω) => F h) (a::h)) =
        pathSum (fun h (_ : Ω) => F h) h+F h := by
      intro h
      simp only [pathSum,mul_add,sum_add_distrib,← sum_mul,K.total,one_mul]
    simp_rw [he]
    rw [historyExpectation_add,ih,sum_range_succ]

theorem history_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (F : List Ω → ℝ)
    (hF : ∀ h ∈ histories Ω T, 0 ≤ F h) (v : ℝ) (hv : 0 < v) :
    (∑ h ∈ histories Ω T, if v ≤ F h then historyWeight K h else 0) ≤
      historyExpectation K T F/v := by
  apply (le_div_iff₀ hv).mpr
  rw [sum_mul]
  apply sum_le_sum
  intro h hh
  split_ifs with hlarge
  · exact mul_le_mul_of_nonneg_left hlarge (historyWeight_nonneg K h)
  · simpa only [zero_mul] using mul_nonneg (historyWeight_nonneg K h) (hF h hh)

end LatinonEntropy

#print axioms LatinonEntropy.history_predictable_sum
#print axioms LatinonEntropy.history_markov
