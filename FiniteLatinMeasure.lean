module

public import LebesgueGridPartition
public import HistoryLatinArray
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

theorem finiteMeasureSum_real_apply {α : Type*} [MeasurableSpace α] {m : ℕ}
    (nu : Fin m → Measure α) [∀ i, IsFiniteMeasure (nu i)] (E : Set α) :
    (∑ i, nu i).real E = ∑ i, (nu i).real E := by
  simp only [measureReal_def,Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun i _ => measure_ne_top (nu i) E)

/-- The finite square as an actual measure: n times the sum over its n^2 boxes. -/
def finiteLatinMeasure {n : ℕ} (L : LatinArray n) : Measure ((I × I) × I) :=
  (n : NNReal) • ∑ x, ∑ y,
    (((volume : Measure I).restrict (lebesgueGridCell x)).prod
      (volume.restrict (lebesgueGridCell y))).prod
        (volume.restrict (lebesgueGridCell (L.val x y)))

instance {n : ℕ} (L : LatinArray n) : IsFiniteMeasure (finiteLatinMeasure L) := by
  unfold finiteLatinMeasure
  infer_instance

/-- The box formula is exact, including sets meeting the grid boundaries. -/
theorem finiteLatinMeasure_real_box {n : ℕ} (L : LatinArray n) (S T U : Set I) :
    (finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ U) =
      (n : ℝ)*∑ x, ∑ y, volume.real (S ∩ lebesgueGridCell x)*
        volume.real (T ∩ lebesgueGridCell y)*volume.real (U ∩ lebesgueGridCell (L.val x y)) := by
  unfold finiteLatinMeasure
  rw [measureReal_nnreal_smul_apply]
  simp only [NNReal.coe_natCast]
  apply congrArg (fun a : ℝ => (n : ℝ)*a)
  rw [finiteMeasureSum_real_apply]
  apply sum_congr rfl
  intro x _
  rw [finiteMeasureSum_real_apply]
  apply sum_congr rfl
  intro y _
  rw [measureReal_prod_prod,measureReal_prod_prod,
    measureReal_restrict_apply' (lebesgueGridCell_measurable x),
    measureReal_restrict_apply' (lebesgueGridCell_measurable y),
    measureReal_restrict_apply' (lebesgueGridCell_measurable (L.val x y))]

end LatinonEntropy

#print axioms LatinonEntropy.finiteMeasureSum_real_apply
#print axioms LatinonEntropy.finiteLatinMeasure_real_box
