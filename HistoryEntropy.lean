module

public import FiniteHistory

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def kernelEntropy {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω) (h : List Ω) : ℝ :=
  -∑ a, K.transition h a*Real.log (K.transition h a)

def historyEntropy {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (K : FiniteKernel Ω) (T : ℕ) : ℝ :=
  -∑ h ∈ histories Ω T, historyWeight K h*Real.log (historyWeight K h)

/-- Zero masses are included, with the usual 0 log 0 convention. -/
theorem mul_log_product (x y : ℝ) :
    (x*y)*Real.log (x*y) = y*(x*Real.log x)+x*(y*Real.log y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

theorem history_entropy_step {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) :
    historyEntropy K (T+1) = historyEntropy K T+historyExpectation K T (kernelEntropy K) := by
  have hlocal : ∀ h : List Ω,
      (∑ a, historyWeight K (a::h)*Real.log (historyWeight K (a::h))) =
        historyWeight K h*Real.log (historyWeight K h)+
          historyWeight K h*(∑ a, K.transition h a*Real.log (K.transition h a)) := by
    intro h
    simp only [historyWeight,mul_log_product,sum_add_distrib,← sum_mul,← mul_sum,K.total,one_mul]
  unfold historyEntropy
  rw [history_sum_succ]
  simp_rw [hlocal]
  rw [sum_add_distrib]
  unfold historyExpectation kernelEntropy
  simp only [mul_neg,sum_neg_distrib]
  ring

theorem history_entropy_chain {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) :
    historyEntropy K T = ∑ t ∈ range T, historyExpectation K t (kernelEntropy K) := by
  induction T with
  | zero => simp [historyEntropy,histories,historyWeight]
  | succ T ih => rw [history_entropy_step,ih,sum_range_succ]

end LatinonEntropy

#print axioms LatinonEntropy.history_entropy_chain
