module

public import LatinTensorLowerBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- An interval bound for all subset sums also bounds any fractional subset. -/
theorem fractional_subset_sum_abs_le {ι : Type*} [Fintype ι]
    (f w : ι → ℝ) (K : ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hcut : ∀ S : Finset ι, |∑ i ∈ S, f i| ≤ K) :
    |∑ i, w i * f i| ≤ K := by
  let P := univ.filter (fun i => 0 ≤ f i)
  let N := univ.filter (fun i => f i < 0)
  have hu : (∑ i, w i * f i) ≤ ∑ i ∈ P, f i := by
    rw [show (∑ i ∈ P, f i) = ∑ i, if 0 ≤ f i then f i else 0 by
      simp only [P,sum_filter]]
    apply sum_le_sum
    intro i _
    by_cases hi : 0 ≤ f i
    · rw [ite_eq_left hi]
      exact (mul_le_mul_of_nonneg_right (hw i).2 hi).trans_eq (one_mul _)
    · rw [ite_eq_right hi]
      exact mul_nonpos_of_nonneg_of_nonpos (hw i).1 (le_of_not_ge hi)
  have hl : (∑ i ∈ N, f i) ≤ ∑ i, w i * f i := by
    rw [show (∑ i ∈ N, f i) = ∑ i, if f i < 0 then f i else 0 by
      simp only [N,sum_filter]]
    apply sum_le_sum
    intro i _
    by_cases hi : f i < 0
    · rw [ite_eq_left hi]
      exact (one_mul (f i)).symm.trans_le
        (mul_le_mul_of_nonpos_right (hw i).2 hi.le)
    · rw [ite_eq_right hi]
      exact mul_nonneg (hw i).1 (le_of_not_gt hi)
  exact abs_le.mpr ⟨(abs_le.mp (hcut N)).1.trans hl,
    hu.trans (abs_le.mp (hcut P)).2⟩

/-- No loss is incurred when all three cut indicators become [0,1] weights. -/
theorem fractional_tensor_cut_abs_le {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → κ → τ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (c : τ → ℝ) (K : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (hc : ∀ k, 0 ≤ c k ∧ c k ≤ 1)
    (hcut : ∀ (S : Finset ι) (T : Finset κ) (U : Finset τ),
      |∑ i ∈ S, ∑ j ∈ T, ∑ k ∈ U, d i j k| ≤ K) :
    |∑ i, ∑ j, ∑ k, a i * b j * c k * d i j k| ≤ K := by
  have hx : (∑ i, ∑ j, ∑ k, a i*b j*c k*d i j k) =
      ∑ i, a i*(∑ j, b j*(∑ k, c k*d i j k)) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    ring
  rw [hx]
  apply fractional_subset_sum_abs_le _ a K ha
  intro S
  have hy : (∑ i ∈ S, ∑ j, b j*(∑ k, c k*d i j k)) =
      ∑ j, b j*(∑ i ∈ S, ∑ k, c k*d i j k) := by
    rw [sum_comm]
    simp only [mul_sum]
  rw [hy]
  apply fractional_subset_sum_abs_le _ b K hb
  intro T
  have hz : (∑ j ∈ T, ∑ i ∈ S, ∑ k, c k*d i j k) =
      ∑ k, c k*(∑ i ∈ S, ∑ j ∈ T, d i j k) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ T, ∑ k, c k*d i j k := sum_comm
      _ = ∑ i ∈ S, ∑ k, ∑ j ∈ T, c k*d i j k :=
        sum_congr rfl (fun i _ => sum_comm)
      _ = ∑ k, ∑ i ∈ S, ∑ j ∈ T, c k*d i j k := sum_comm
      _ = _ := by simp only [mul_sum]
  rw [hz]
  apply fractional_subset_sum_abs_le _ c K hc
  intro U
  have he : (∑ k ∈ U, ∑ i ∈ S, ∑ j ∈ T, d i j k) =
      ∑ i ∈ S, ∑ j ∈ T, ∑ k ∈ U, d i j k := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    exact sum_comm
  rw [he]
  exact hcut S T U

end LatinonEntropy

#print axioms LatinonEntropy.fractional_subset_sum_abs_le
#print axioms LatinonEntropy.fractional_tensor_cut_abs_le
