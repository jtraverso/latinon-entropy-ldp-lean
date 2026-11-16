module

public import LatinonBridge.LatinonCompactness
public import CompactUniformLatinonUpper
public import LatinonRegularization
public import LatinonFullDyadicKL

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

/-- Every rate sublevel is compact in the original full Latinon topology.
The extended rate is retained,including the value infinity. -/
theorem latinon_rate_sublevels_compact (r : ℝ≥0∞) : IsCompact {W : LatinonMeasure | latinonRate W ≤ r} :=
  (latinon_rate_lowerSemicontinuous.isClosed_preimage r).isCompact

/-- Global closed-set upper bound,with a NONSTRICT rate threshold and an
arbitrarily small exponent slack. It includes zero-rate and infinite-rate cases. -/
theorem closed_uniform_latinon_upper (F : Set LatinonMeasure) (hF : IsClosed F)
    (t : ℝ) (ht : ∀ W ∈ F, ENNReal.ofReal t ≤ latinonRate W) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (uniformLatinonLaw (hN.trans_le hn)).real F ≤ Real.exp ((n : ℝ)^2*(-t+eps)) := by
  by_cases hsmall : t ≤ eps
  · refine ⟨1,by decide,?_⟩
    intro n hn
    let _ : IsProbabilityMeasure (uniformLatinonLaw (Nat.zero_lt_one.trans_le hn)) :=
      uniformLatinonLaw_probability _
    calc
      _ ≤ 1 := (probability_real_set_bounds _ F).2
      _ ≤ Real.exp ((n : ℝ)^2*(-t+eps)) := by
        have h : 0 ≤ (n : ℝ)^2*(-t+eps) := mul_nonneg (sq_nonneg _) (by linarith only [hsmall])
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h
  · have htpos : 0 < t := heps.trans (lt_of_not_ge hsmall)
    have hstrict : ENNReal.ofReal (t-eps/2) < ENNReal.ofReal t :=
      ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith only [heps],htpos⟩
    obtain ⟨N,hN,hbound⟩ := compact_uniform_latinon_upper F (latinon_closed_set_compact F hF)
      (t-eps/2) (fun W hW => hstrict.trans_le (ht W hW)) (eps/2) (half_pos heps)
    refine ⟨N,hN,?_⟩
    intro n hn
    have he : -(t-eps/2)+eps/2 = -t+eps := by ring
    simpa only [he] using hbound n hn

/-- Global open-set lower bound in the matching finite-threshold form.
The nonnegative threshold and positive slack retain all extended-rate cases. -/
theorem open_uniform_latinon_lower (G : Set LatinonMeasure) (hG : IsOpen G)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : ∃ W ∈ G, latinonRate W ≤ ENNReal.ofReal t)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp (-(n : ℝ)^2*(t+eps)) ≤ (uniformLatinonLaw (hN.trans_le hn)).real G := by
  apply open_uniform_latinon_lower_threshold G hG (t+eps)
  obtain ⟨W,hW,hRate⟩ := ht
  refine ⟨W,hW,hRate.trans_lt ?_⟩
  apply ENNReal.ofReal_lt_ofReal_iff'.mpr
  constructor <;> linarith only [ht0,heps]

end LatinonEntropy

#print axioms LatinonEntropy.latinon_rate_sublevels_compact
#print axioms LatinonEntropy.closed_uniform_latinon_upper
#print axioms LatinonEntropy.open_uniform_latinon_lower
