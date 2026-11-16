module

public import FiniteLatinMeasureMargins
public import AlignedIntervalIntegrals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

def unitSymbolInterval (a b : ℝ) : Set I := ((↑) : I → ℝ) ⁻¹' Set.Ioc a b

theorem unitSymbolInterval_measurable (a b : ℝ) : MeasurableSet (unitSymbolInterval a b) :=
  measurableSet_Ioc.preimage measurable_subtype_coe

theorem lebesgueGridCell_interval_image {n : ℕ} (hn : 0 < n) (z : Fin n) (a b : ℝ) :
    ((↑) : I → ℝ) '' (unitSymbolInterval a b ∩ lebesgueGridCell z) =
      symbolGridCell z ∩ Set.Ioc a b := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨hu.2,hu.1⟩
  · intro hx
    exact ⟨⟨x,symbolGridCell_subset_unit hn z hx.1⟩,⟨hx.2,hx.1⟩,rfl⟩

theorem symbolIntervalWeight_eq_grid_interval_measure {n : ℕ} (hn : 0 < n) (z : Fin n) (a b : ℝ) :
    symbolIntervalWeight z a b =
      (n : ℝ)*volume.real (unitSymbolInterval a b ∩ lebesgueGridCell z) := by
  unfold symbolIntervalWeight
  apply congrArg (fun c : ℝ => (n : ℝ)*c)
  simp only [measureReal_def]
  rw [unitInterval.volume_apply,lebesgueGridCell_interval_image hn z a b]

/-- The actual finite Latinon measure has exactly the step cut integrals. -/
theorem latinArrayToLatinonMeasure_interval_integral {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (S T : Set I) (a b : ℝ) :
    (latinArrayToLatinonMeasure hn L).measure.real ((S ×ˢ T) ×ˢ unitSymbolInterval a b) =
      ∫ u in S, ∫ v in T, finiteLatinIntervalStep L a b u v := by
  change (finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ unitSymbolInterval a b) = _
  rw [finiteLatinMeasure_real_box]
  unfold finiteLatinIntervalStep
  rw [finiteRectangleStep_rectangle_integral volume S T lebesgueGridCell lebesgueGridCell
    lebesgueGridCell_measurable lebesgueGridCell_measurable]
  simp_rw [symbolIntervalWeight_eq_grid_interval_measure hn]
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  ring

theorem latinArrayToLatinonMeasure_identity_block_table {n r s t : ℕ} (hn : 0 < n)
    (P : SymbolIntervalPartition t)
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (L : LatinArray n) (z : LatinBlock r s t) :
    (latinArrayToLatinonMeasure hn L).measure.real
      ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2)) =
      alignedLatinIntervalTable P A B id id L z :=
  (latinArrayToLatinonMeasure_interval_integral hn L _ _ _ _).trans
    (aligned_finite_interval_integral_eq_table hn P A B id id
      (MeasurePreserving.id volume) (MeasurePreserving.id volume) L z)

end LatinonEntropy

#print axioms LatinonEntropy.unitSymbolInterval_measurable
#print axioms LatinonEntropy.lebesgueGridCell_interval_image
#print axioms LatinonEntropy.symbolIntervalWeight_eq_grid_interval_measure
#print axioms LatinonEntropy.latinArrayToLatinonMeasure_interval_integral
#print axioms LatinonEntropy.latinArrayToLatinonMeasure_identity_block_table
#print axioms LatinonEntropy.LatinonMeasure.xy_uniform_real
#print axioms LatinonEntropy.LatinonMeasure.xz_uniform_real
#print axioms LatinonEntropy.LatinonMeasure.yz_uniform_real
#print axioms LatinonEntropy.uniformLatinonMeasure
#print axioms LatinonEntropy.finiteMeasureSum_real_apply
#print axioms LatinonEntropy.finiteLatinMeasure_real_box
#print axioms LatinonEntropy.lebesgueGrid_inter_sum
#print axioms LatinonEntropy.finiteLatinMeasure_xy_real
#print axioms LatinonEntropy.finiteLatinMeasure_xz_real
#print axioms LatinonEntropy.finiteLatinMeasure_yz_real
#print axioms LatinonEntropy.finiteLatinMeasure_xy
#print axioms LatinonEntropy.finiteLatinMeasure_xz
#print axioms LatinonEntropy.finiteLatinMeasure_yz
#print axioms LatinonEntropy.latinArrayToLatinonMeasure
#print axioms LatinonEntropy.finiteLatinMeasure_probability
