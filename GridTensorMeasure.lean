module

public import FiniteLatinMeasureMargins
public import ProfileFluid

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

/-- The actual measure of a nonnegative grid profile; its box density is n*p. -/
def gridTensorMeasure {n : ℕ} (p : Fin n → Fin n → Fin n → ℝ) : Measure LatinonPoint :=
  ∑ x, ∑ y, ∑ z, (Real.toNNReal ((n : ℝ)*p x y z)) •
    ((((volume : Measure I).restrict (lebesgueGridCell x)).prod
      (volume.restrict (lebesgueGridCell y))).prod
        (volume.restrict (lebesgueGridCell z)))

instance {n : ℕ} (p : Fin n → Fin n → Fin n → ℝ) :
    IsFiniteMeasure (gridTensorMeasure p) := by
  unfold gridTensorMeasure
  infer_instance

theorem gridTensorMeasure_real_box {n : ℕ} (p : Fin n → Fin n → Fin n → ℝ)
    (hp : ∀ x y z, 0 ≤ p x y z) (S T U : Set I) :
    (gridTensorMeasure p).real ((S ×ˢ T) ×ˢ U) =
      (n : ℝ) * ∑ x, ∑ y, ∑ z, p x y z *
        volume.real (S ∩ lebesgueGridCell x) *
        volume.real (T ∩ lebesgueGridCell y) *
        volume.real (U ∩ lebesgueGridCell z) := by
  unfold gridTensorMeasure
  rw [finiteMeasureSum_real_apply,mul_sum]
  apply sum_congr rfl
  intro x _
  rw [finiteMeasureSum_real_apply,mul_sum]
  apply sum_congr rfl
  intro y _
  rw [finiteMeasureSum_real_apply,mul_sum]
  apply sum_congr rfl
  intro z _
  rw [measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg _) (hp x y z)),
    measureReal_prod_prod,measureReal_prod_prod,
    measureReal_restrict_apply' (lebesgueGridCell_measurable x),
    measureReal_restrict_apply' (lebesgueGridCell_measurable y),
    measureReal_restrict_apply' (lebesgueGridCell_measurable z)]
  ring

/-- Every coordinate slice integrates out by its unit line sum. -/
theorem gridTensorMeasure_xy_real {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hrow : ∀ x y, ∑ z, p x y z = 1) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (gridTensorMeasure p).real ((S ×ˢ T) ×ˢ Set.univ) = volume.real S*volume.real T := by
  rw [gridTensorMeasure_real_box p hp]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  have hr : ∀ x y, (∑ z, p x y z*volume.real (S ∩ lebesgueGridCell x)*
      volume.real (T ∩ lebesgueGridCell y)*(1/(n : ℝ))) =
      volume.real (S ∩ lebesgueGridCell x)*volume.real (T ∩ lebesgueGridCell y)/(n : ℝ) := by
    intro x y
    rw [← sum_mul,← sum_mul,← sum_mul,hrow]
    ring
  simp_rw [hr]
  simp only [← sum_div]
  rw [← sum_mul_sum,
    lebesgueGrid_inter_sum hn S hS,lebesgueGrid_inter_sum hn T hT]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem gridTensorMeasure_xz_real {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hcol : ∀ x z, ∑ y, p x y z = 1) (S U : Set I)
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (gridTensorMeasure p).real ((S ×ˢ Set.univ) ×ˢ U) = volume.real S*volume.real U := by
  rw [gridTensorMeasure_real_box p hp]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  have hr : ∀ x, (∑ y, ∑ z, p x y z*volume.real (S ∩ lebesgueGridCell x)*
      (1/(n : ℝ))*volume.real (U ∩ lebesgueGridCell z)) =
      ∑ z : Fin n, volume.real (S ∩ lebesgueGridCell x)*volume.real (U ∩ lebesgueGridCell z)/(n : ℝ) := by
    intro x
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    rw [← sum_mul,← sum_mul,← sum_mul,hcol]
    ring
  simp_rw [hr]
  simp only [← sum_div]
  rw [← sum_mul_sum,
    lebesgueGrid_inter_sum hn S hS,lebesgueGrid_inter_sum hn U hU]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem gridTensorMeasure_yz_real {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (htime : ∀ y z, ∑ x, p x y z = 1) (T U : Set I)
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (gridTensorMeasure p).real ((Set.univ ×ˢ T) ×ˢ U) = volume.real T*volume.real U := by
  rw [gridTensorMeasure_real_box p hp]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  rw [sum_comm]
  have hr : ∀ y, (∑ x, ∑ z, p x y z*(1/(n : ℝ))*
      volume.real (T ∩ lebesgueGridCell y)*volume.real (U ∩ lebesgueGridCell z)) =
      ∑ z : Fin n, volume.real (T ∩ lebesgueGridCell y)*volume.real (U ∩ lebesgueGridCell z)/(n : ℝ) := by
    intro y
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    rw [← sum_mul,← sum_mul,← sum_mul,htime]
    ring
  simp_rw [hr]
  simp only [← sum_div]
  rw [← sum_mul_sum,
    lebesgueGrid_inter_sum hn T hT,lebesgueGrid_inter_sum hn U hU]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

/-- No marginal condition is assumed on the resulting measure: all three
are proved from the three finite line sums. -/
def gridTensorToLatinonMeasure {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hrow : ∀ x y, ∑ z, p x y z = 1)
    (hcol : ∀ x z, ∑ y, p x y z = 1)
    (htime : ∀ y z, ∑ x, p x y z = 1) : LatinonMeasure where
  measure := gridTensorMeasure p
  order := id
  order_preserving := MeasurePreserving.id volume
  xy_uniform := by
    intro S T hS hT
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simpa only [measureReal_def,ENNReal.toReal_mul] using
      gridTensorMeasure_xy_real hn p hp hrow S T hS hT
  xz_uniform := by
    intro S U hS hU
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simpa only [measureReal_def,ENNReal.toReal_mul] using
      gridTensorMeasure_xz_real hn p hp hcol S U hS hU
  yz_uniform := by
    intro T U hT hU
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simpa only [measureReal_def,ENNReal.toReal_mul] using
      gridTensorMeasure_yz_real hn p hp htime T U hT hU

end LatinonEntropy

#print axioms LatinonEntropy.gridTensorMeasure_real_box
#print axioms LatinonEntropy.gridTensorMeasure_xy_real
#print axioms LatinonEntropy.gridTensorMeasure_xz_real
#print axioms LatinonEntropy.gridTensorMeasure_yz_real
#print axioms LatinonEntropy.gridTensorToLatinonMeasure
