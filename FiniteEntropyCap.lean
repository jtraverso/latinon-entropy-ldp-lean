module

public import WeightedChain

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem weighted_entropy_lower_of_point_cap {A : Type*} (S : Finset A)
    (w : A → ℝ) (hw : ∀ a ∈ S, 0 < w a) (htotal : ∑ a ∈ S, w a = 1)
    (N : ℝ) (hN : 0 < N) (hcap : ∀ a ∈ S, w a ≤ 1/N) :
    Real.log N ≤ weightedFamilyEntropy S w := by
  have hl : ∀ a ∈ S, Real.log (w a) ≤ -Real.log N := by
    intro a ha
    have h := Real.log_le_log (hw a ha) (hcap a ha)
    simpa only [Real.log_div one_ne_zero hN.ne',Real.log_one,zero_sub] using h
  have hs := sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hl a ha) (hw a ha).le)
  rw [← sum_mul,htotal,one_mul] at hs
  unfold weightedFamilyEntropy
  rw [htotal,Real.log_one,mul_zero,zero_sub]
  linarith only [hs]

end LatinonEntropy

#print axioms LatinonEntropy.weighted_entropy_lower_of_point_cap
