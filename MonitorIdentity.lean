module

public import HazardMonitor

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- Exact monitor transform. The discrepancy recursion supplies the
correction for all later rows; no independence or concentration is used. -/
theorem hazard_monitor_identity (H E D w : ℕ → ℝ) (hzero : D 0 = 0)
    (hstep : ∀ t, D (t+1) = D t*(1-H t)-E t) (T : ℕ) :
    (∑ x ∈ range T, w x*(E x+H x*D x)) =
      ∑ s ∈ range T, hazardMonitor H w s T*E s := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hg : ∀ s ∈ range T, hazardMonitor H w s (T+1) =
        hazardMonitor H w s T-propagationKernel H s T*H T*w T := by
      intro s hs
      have hsT : s+1 ≤ T := by have := mem_range.mp hs; omega
      simp only [hazardMonitor,sum_Ico_succ_top hsT]
      ring
    have hlast : hazardMonitor H w T (T+1) = w T := by simp [hazardMonitor]
    have hsum : (∑ s ∈ range T, hazardMonitor H w s (T+1)*E s) =
        (∑ s ∈ range T, hazardMonitor H w s T*E s)-
          (H T*w T)*(∑ s ∈ range T, propagationKernel H s T*E s) := by
      calc
        _ = ∑ s ∈ range T, (hazardMonitor H w s T*E s-
            (H T*w T)*(propagationKernel H s T*E s)) := by
          apply sum_congr rfl
          intro s hs
          rw [hg s hs]
          ring
        _ = _ := by simp only [sum_sub_distrib,mul_sum]
    rw [sum_range_succ,sum_range_succ,ih,hlast,hsum,fluid_defect_telescope H E D hzero hstep T]
    ring

end LatinonEntropy

#print axioms LatinonEntropy.hazard_monitor_identity
