module

public import FluidStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- The total future response to one error is at most one. -/
theorem propagation_hazard_telescope (H : ℕ → ℝ) (s T : ℕ) :
    (∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x) = 1-propagationKernel H s T := by
  induction T with
  | zero => simp [propagationKernel]
  | succ T ih =>
    by_cases hs : s+1 ≤ T
    · have hk : propagationKernel H s (T+1) = propagationKernel H s T*(1-H T) :=
        prod_Ico_succ_top hs _
      rw [sum_Ico_succ_top hs _,hk,ih]
      ring
    · have hle : T+1 ≤ s+1 := by omega
      have hempty : Ico (s+1) (T+1) = ∅ := Ico_eq_empty_of_le hle
      simp [propagationKernel,hempty]

theorem propagation_hazard_budget (H : ℕ → ℝ) (hH : ∀ x, 0 ≤ H x ∧ H x ≤ 1)
    (s T : ℕ) : (∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x) ≤ 1 := by
  rw [propagation_hazard_telescope]
  linarith only [(propagationKernel_bounds H hH s T).1]

def hazardMonitor (H w : ℕ → ℝ) (s T : ℕ) : ℝ :=
  w s-∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x*w x

theorem hazardMonitor_abs_le_two (H w : ℕ → ℝ) (hH : ∀ x, 0 ≤ H x ∧ H x ≤ 1)
    (hw : ∀ x, |w x| ≤ 1) (s T : ℕ) : |hazardMonitor H w s T| ≤ 2 := by
  have hb : |∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x*w x| ≤ 1 := by
    calc
      _ ≤ ∑ x ∈ Ico (s+1) T, |propagationKernel H s x*H x*w x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x := by
        apply sum_le_sum
        intro x _
        have hnn : 0 ≤ propagationKernel H s x*H x :=
          mul_nonneg (propagationKernel_bounds H hH s x).1 (hH x).1
        rw [abs_mul,abs_of_nonneg hnn]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw x) hnn
      _ ≤ 1 := propagation_hazard_budget H hH s T
  calc
    _ ≤ |w s|+|∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x*w x| := by
      simpa only [hazardMonitor,sub_eq_add_neg,abs_neg] using
        abs_add_le (w s) (-(∑ x ∈ Ico (s+1) T, propagationKernel H s x*H x*w x))
    _ ≤ 2 := by linarith only [hw s,hb]

end LatinonEntropy

#print axioms LatinonEntropy.propagation_hazard_telescope
#print axioms LatinonEntropy.hazardMonitor_abs_le_two
