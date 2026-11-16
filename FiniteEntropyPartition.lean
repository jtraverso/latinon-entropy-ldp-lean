module

public import FiniteBlockEntropy
public import UniformPushforward

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem finite_partition_entropy_upper {I K : Type*} [DecidableEq I] [DecidableEq K]
    (T : Finset I) (color : I → K) (x : I → ℝ) (hx : ∀ i ∈ T, 0 ≤ x i) :
    -(∑ i ∈ T, x i*Real.log (x i)) ≤ ∑ k ∈ T.image color,
      ((∑ i ∈ finiteImageFiber T color k, x i)*Real.log ((finiteImageFiber T color k).card : ℝ)-
        (∑ i ∈ finiteImageFiber T color k, x i)*Real.log (∑ i ∈ finiteImageFiber T color k, x i)) := by
  have hs : (∑ i ∈ T, x i*Real.log (x i)) = ∑ k ∈ T.image color,
      ∑ i ∈ finiteImageFiber T color k, x i*Real.log (x i) := by
    simpa only [finiteImageFiber] using sum_by_coordinate T color (fun (_ : K) i => x i*Real.log (x i))
  rw [hs,← sum_neg_distrib]
  apply sum_le_sum
  intro k hk
  have hne : (finiteImageFiber T color k).Nonempty := by
    obtain ⟨i,hi,hic⟩ := mem_image.mp hk
    refine ⟨i,?_⟩
    simp only [finiteImageFiber,mem_filter]
    exact ⟨hi,hic⟩
  have hnonneg : ∀ i ∈ finiteImageFiber T color k, 0 ≤ x i := by
    intro i hi
    simp only [finiteImageFiber,mem_filter] at hi
    exact hx i hi.1
  exact finite_block_entropy_upper _ hne x hnonneg

theorem block_entropy_scaled_identity (N C mass : ℝ) (hN : 0 < N) (hC : 0 < C) (hm : 0 ≤ mass) :
    mass*Real.log C-mass*Real.log mass =
      mass*Real.log N+mass*Real.log ((C/N^3)/(mass/N^2)) := by
  by_cases hz : mass = 0
  · simp [hz]
  · have hp : 0 < mass := lt_of_le_of_ne hm (Ne.symm hz)
    rw [Real.log_div (div_pos hC (pow_pos hN 3)).ne' (div_pos hp (pow_pos hN 2)).ne',
      Real.log_div hC.ne' (pow_ne_zero 3 hN.ne'),
      Real.log_div hp.ne' (pow_ne_zero 2 hN.ne'),Real.log_pow,Real.log_pow]
    ring

end LatinonEntropy

#print axioms LatinonEntropy.finite_partition_entropy_upper
#print axioms LatinonEntropy.block_entropy_scaled_identity
