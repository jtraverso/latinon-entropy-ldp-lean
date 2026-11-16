module

public import OrderPermutationL1
public import UnitGridL1Approximation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Every actual MP order map is approximated by exact interval-permutation
bijections for every sufficiently large size, rather than just dyadic sizes. -/
theorem exists_all_sizes_order_permutation_L1 (f : I → I)
    (hf : MeasurePreserving f volume volume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∃ sigma : Equiv.Perm (Fin n),
        MeasurePreserving (gridIntervalPermutation (hN.trans_le hn) sigma) volume volume ∧
        (∫ u : I, |(f u : ℝ)-(gridIntervalPermutation (hN.trans_le hn) sigma u : ℝ)|) ≤ eps := by
  have hquarter : 0 < eps/4 := by positivity
  obtain ⟨NS,hNS,hstep⟩ := exists_all_sizes_grid_step_L1 (fun u => (f u : ℝ))
    (integrable_unit_coordinate f hf.measurable) (eps/4) hquarter
  obtain ⟨K,hK⟩ := exists_nat_gt (4/eps)
  let N := max NS (K+1)
  have hN : 0 < N := hNS.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnpos : 0 < n := hN.trans_le hn
  have hnS : NS ≤ n := (le_max_left _ _).trans hn
  have hnK : K+1 ≤ n := (le_max_right _ _).trans hn
  have hlarge : 4/eps < (n : ℝ) := hK.trans (by exact_mod_cast (show K < n by omega))
  have hinv : 1/(n : ℝ) < eps/4 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hnpos : (0 : ℝ) < n)).mpr
    have hprod := (div_lt_iff₀ heps).mp hlarge
    nlinarith only [hprod]
  obtain ⟨a,_,hE⟩ := hstep n hnS
  obtain ⟨sigma,hsigma⟩ := exists_grid_permutation_L1_bound hnpos f hf a
  refine ⟨sigma,gridIntervalPermutation_preserves hnpos sigma,?_⟩
  simp only [div_eq_mul_inv,one_mul] at hsigma hinv
  linarith only [hsigma,hE,hinv]

end LatinonEntropy

#print axioms LatinonEntropy.exists_all_sizes_order_permutation_L1
