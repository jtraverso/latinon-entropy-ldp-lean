module

public import OrderAssignmentCost
public import LebesgueGridPartition

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Matrix Finset
open scoped Classical unitInterval

def orderGridTransport (f : I → I) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (n : ℝ)*(volume : Measure I).real (lebesgueGridCell i ∩ f ⁻¹' lebesgueGridCell j)

/-- This stochastic transport is derived from the actual order map;
none of its row or column constraints are extra hypotheses. -/
theorem order_grid_transport_doublyStochastic {n : ℕ} (hn : 0 < n)
    (f : I → I) (hf : MeasurePreserving f volume volume) :
    orderGridTransport f n ∈ doublyStochastic ℝ (Fin n) := by
  let G := lebesgueGridPartition n hn
  have hG : ∀ i, (volume : Measure I).real (G.cell i) = 1/(n : ℝ) :=
    fun i => lebesgueGridCell_mass hn i
  have he : ∀ i j, orderGridTransport f n i j = alignedPartitionWeight G G f j i :=
    fun _ _ => rfl
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_,?_,?_⟩
  · intro i j
    rw [he]
    exact alignedPartitionWeight_nonneg G G f j i
  · intro i
    simp_rw [he]
    have hm := alignedPartitionWeight_mean hn G G f hf i
    rw [hG] at hm
    have hR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne'
    have heq := (div_eq_iff hR).mp hm
    simpa only [one_div,inv_mul_cancel₀ hR] using heq
  · intro j
    simp_rw [he]
    exact alignedPartitionWeight_row hn G G hG f hf j

theorem exists_order_grid_permutation_cost_le {n : ℕ} (hn : 0 < n)
    (f : I → I) (hf : MeasurePreserving f volume volume) (c : Matrix (Fin n) (Fin n) ℝ) :
    ∃ sigma : Equiv.Perm (Fin n), (∑ i, c i (sigma i)) ≤
      ∑ i, ∑ j, orderGridTransport f n i j*c i j :=
  exists_permutation_cost_le_fractional _ c (order_grid_transport_doublyStochastic hn f hf)

end LatinonEntropy

#print axioms LatinonEntropy.order_grid_transport_doublyStochastic
#print axioms LatinonEntropy.exists_order_grid_permutation_cost_le
#print axioms LatinonEntropy.matrixAssignmentCost
#print axioms LatinonEntropy.exists_permutation_cost_le_fractional
