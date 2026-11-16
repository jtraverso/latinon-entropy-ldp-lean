module

public import LatinBlockMass

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- The marginal entropy is bounded by the entropy of its actual normalized
block table. Zero block masses are allowed; only active fibres enter the sum. -/
theorem latin_marginal_entropy_le_coarse {n r s q : ℕ} (hn : 0 < n)
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 ≤ w L)
    (htotal : ∑ L ∈ S, w L = 1)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    latinMarginalEntropy S w ≤ (n : ℝ)^2*Real.log (n : ℝ)+
      (n : ℝ)^2*latinLawCoarseEntropy S w row col sym := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hraw : latinMarginalEntropy S w ≤ ∑ b ∈ latinActiveBlocks row col sym,
      (latinLawBlockMass S w row col sym b*Real.log ((latinBlockFiber row col sym b).card : ℝ)-
        latinLawBlockMass S w row col sym b*Real.log (latinLawBlockMass S w row col sym b)) := by
    have h := finite_partition_entropy_upper (univ : Finset (LatinTriple n))
      (latinTripleBlock row col sym) (latinTripleWeight S w)
      (fun t _ => latinFamilyMarginal_nonneg S w hw t.1 t.2)
    change -(∑ t : LatinTriple n, latinTripleWeight S w t*Real.log (latinTripleWeight S w t)) ≤
      ∑ b ∈ latinActiveBlocks row col sym,
        ((∑ t ∈ latinBlockFiber row col sym b, latinTripleWeight S w t)*
            Real.log ((latinBlockFiber row col sym b).card : ℝ)-
          (∑ t ∈ latinBlockFiber row col sym b, latinTripleWeight S w t)*
            Real.log (∑ t ∈ latinBlockFiber row col sym b, latinTripleWeight S w t)) at h
    simp_rw [← latin_law_block_mass_eq_fiber_sum] at h
    rw [← latin_marginal_entropy_eq_triple_sum] at h
    exact h
  apply hraw.trans_eq
  calc
    _ = ∑ b ∈ latinActiveBlocks row col sym,
        (latinLawBlockMass S w row col sym b*Real.log (n : ℝ)+
          latinLawBlockMass S w row col sym b*
            Real.log (latinBlockVolume row col sym b/latinLawBlockTable S w row col sym b)) := by
      apply sum_congr rfl
      intro b hb
      have hC : (0 : ℝ) < (latinBlockFiber row col sym b).card :=
        Nat.cast_pos.mpr (card_pos.mpr (latinBlockFiber_nonempty row col sym b hb))
      exact block_entropy_scaled_identity (n : ℝ) _ _ hnR hC
        (latin_law_block_mass_nonneg S w hw row col sym b)
    _ = _ := by
      rw [sum_add_distrib,← sum_mul,latin_law_block_mass_total S w htotal]
      congr 1
      unfold latinLawCoarseEntropy
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [← mul_assoc]
      congr 1
      unfold latinLawBlockTable
      field_simp [hnR.ne']

end LatinonEntropy
