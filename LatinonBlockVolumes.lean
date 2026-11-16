module

public import LatinonBallRounding
public import LatinBlockGeometry

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

theorem abs_mul_unit_le (a b : ℝ) (hb : 0 ≤ b ∧ b ≤ 1) : |a*b| ≤ |a| := by
  rw [abs_mul,abs_of_nonneg hb.1]
  exact (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg a)).trans_eq (mul_one _)

theorem unit_product_three_abs_sub_le (a b c A B C : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hA : 0 ≤ A ∧ A ≤ 1) (hB : 0 ≤ B ∧ B ≤ 1) :
    |a*b*c-A*B*C| ≤ |a-A|+|b-B|+|c-C| := by
  have he : a*b*c-A*B*C = (a-A)*b*c+(b-B)*A*c+(c-C)*A*B := by ring
  rw [he]
  calc
    _ ≤ |(a-A)*b*c|+|(b-B)*A*c|+|(c-C)*A*B| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add
      ((abs_mul_unit_le _ _ hc).trans (abs_mul_unit_le _ _ hb))
      ((abs_mul_unit_le _ _ hc).trans (abs_mul_unit_le _ _ hA)))
      ((abs_mul_unit_le _ _ hB).trans (abs_mul_unit_le _ _ hA))

theorem finite_class_proportion_bounds {n q : ℕ} (hn : 0 < n)
    (label : Fin n → Fin q) (a : Fin q) :
    0 ≤ ((univ.filter (fun x => label x = a)).card : ℝ)/(n : ℝ) ∧
      ((univ.filter (fun x => label x = a)).card : ℝ)/(n : ℝ) ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  refine ⟨div_nonneg (Nat.cast_nonneg _) hnR.le,?_⟩
  apply (div_le_one hnR).mpr
  exact_mod_cast (show (univ.filter (fun x => label x = a)).card ≤ n from
    (card_le_card (filter_subset _ _)).trans_eq (by simp))

def latinonPartitionVolume {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t) (z : LatinBlock r s t) : ℝ :=
  volume.real (A.cell z.1.1)*volume.real (B.cell z.1.2)*(P.right z.2-P.left z.2)

def latinonPartitionTable (W : LatinonMeasure) {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t) (z : LatinBlock r s t) : ℝ :=
  W.measure.real ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ
    unitSymbolInterval (P.left z.2) (P.right z.2))

theorem latinon_partition_volume_pos {r s t : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t)
    (hA : ∀ a, 0 < volume.real (A.cell a)) (hB : ∀ b, 0 < volume.real (B.cell b))
    (z : LatinBlock r s t) : 0 < latinonPartitionVolume A B P z :=
  mul_pos (mul_pos (hA _) (hB _)) (sub_pos.mpr (P.left_lt_right _))

theorem rounded_latin_block_volume_error {n r s t : ℕ} (hn : 0 < n)
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (P : SymbolIntervalPartition t) (row : Fin n → Fin r) (col : Fin n → Fin s)
    (tau : ℝ)
    (hr : ∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-volume.real (A.cell a)| < tau)
    (hc : ∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-volume.real (B.cell b)| < tau)
    (z : LatinBlock r s t) :
    |latinBlockVolume row col (P.color n) z-latinonPartitionVolume A B P z| <
      2*tau+1/(n : ℝ) := by
  rcases z with ⟨⟨i,j⟩,k⟩
  rw [latin_block_volume_product]
  have h := unit_product_three_abs_sub_le
    (((univ.filter (fun x => row x = i)).card : ℝ)/(n : ℝ))
    (((univ.filter (fun y => col y = j)).card : ℝ)/(n : ℝ))
    (((univ.filter (fun z => P.color n z = k)).card : ℝ)/(n : ℝ))
    (volume.real (A.cell i)) (volume.real (B.cell j)) (P.right k-P.left k)
    (finite_class_proportion_bounds hn col j) (finite_class_proportion_bounds hn (P.color n) k)
    (probability_real_set_bounds volume (A.cell i)) (probability_real_set_bounds volume (B.cell j))
  have hs := P.color_class_proportion_error hn k
  have hri := hr i
  have hcj := hc j
  change |_-volume.real (A.cell i)*volume.real (B.cell j)*(P.right k-P.left k)| < _
  linarith only [h,hs,hri,hcj]

end LatinonEntropy

#print axioms LatinonEntropy.abs_mul_unit_le
#print axioms LatinonEntropy.unit_product_three_abs_sub_le
#print axioms LatinonEntropy.finite_class_proportion_bounds
#print axioms LatinonEntropy.latinon_partition_volume_pos
#print axioms LatinonEntropy.rounded_latin_block_volume_error
