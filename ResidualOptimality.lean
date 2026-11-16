module

public import CorrectionOptimizer

@[expose] public section

/-! The local L1 inequality behind the no-negative-closed-walk argument.
At Q=M both arc costs are +1. If a walk uses both orientations of one
coordinate, cancellation can lower the actual variation; it never raises
it beyond the sum of its arc costs. -/

noncomputable section

namespace LatinonEntropy

def forwardCost (q m : ℝ) : ℝ := if q < m then -1 else 1
def backwardCost (q m : ℝ) : ℝ := if m < q then -1 else 1

theorem abs_step_le_residual_cost
    (q m a b delta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ delta)
    (hbelow : q < m → q + delta * (a - b) ≤ m)
    (habove : m < q → m ≤ q + delta * (a - b)) :
    |q + delta * (a - b) - m| - |q - m| ≤
      delta * (a * forwardCost q m + b * backwardCost q m) := by
  by_cases hlt : q < m
  · have hn : ¬m < q := not_lt_of_ge hlt.le
    have hs : q + delta * (a - b) - m ≤ 0 := by linarith [hbelow hlt]
    simp only [forwardCost, backwardCost, ite_eq_left hlt, ite_eq_right hn,
      abs_of_nonpos hs, abs_of_neg (sub_neg.mpr hlt)]
    ring_nf
    exact le_rfl
  · by_cases hgt : m < q
    · have hs : 0 ≤ q + delta * (a - b) - m := by linarith [habove hgt]
      simp only [forwardCost, backwardCost, ite_eq_right hlt, ite_eq_left hgt,
        abs_of_nonneg hs, abs_of_pos (sub_pos.mpr hgt)]
      ring_nf
      exact le_rfl
    · have heq : q = m := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      subst q
      have hab : |a - b| ≤ a + b := abs_le.mpr ⟨by linarith, by linarith⟩
      have hs : m + delta * (a - b) - m = delta * (a - b) := by ring
      simp only [forwardCost, backwardCost, lt_self_iff_false, ite_false,
        sub_self, abs_zero, sub_zero, mul_one, hs, abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left hab hd

/-- Any concrete nondecreasing perturbation has nonnegative total residual
cost. The feasible positive step and the no-crossing conditions are explicit;
the uniform small-step construction for a residual walk is a later lemma. -/
theorem nonnegative_residual_cost_of_step
    {I : Type*} [Fintype I] (q m a b : I → ℝ) (delta : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hd : 0 < delta)
    (hbelow : ∀ i, q i < m i → q i + delta * (a i - b i) ≤ m i)
    (habove : ∀ i, m i < q i → m i ≤ q i + delta * (a i - b i))
    (hminimal : (∑ i, |q i - m i|) ≤ ∑ i, |q i + delta * (a i - b i) - m i|) :
    0 ≤ ∑ i : I, (a i * forwardCost (q i) (m i) + b i * backwardCost (q i) (m i)) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    abs_step_le_residual_cost (q i) (m i) (a i) (b i) delta
      (ha i) (hb i) hd.le (hbelow i) (habove i))
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hn : 0 ≤ delta *
      (∑ i : I, (a i * forwardCost (q i) (m i) + b i * backwardCost (q i) (m i))) := by
    linarith
  exact nonneg_of_mul_nonneg_right hn hd

end LatinonEntropy

#print axioms LatinonEntropy.abs_step_le_residual_cost
#print axioms LatinonEntropy.nonnegative_residual_cost_of_step
