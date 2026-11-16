module

public import MeasurableAlignmentWeights
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev LatinonPoint := (I × I) × I

/-- The measure representation of a Latinon (Garbe et al., Definition 3.16).
All three two-coordinate marginals are uniform; the order map is retained. -/
structure LatinonMeasure where
  measure : Measure LatinonPoint
  order : I → I
  order_preserving : MeasurePreserving order volume volume
  xy_uniform : ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
    measure ((S ×ˢ T) ×ˢ Set.univ) = volume S * volume T
  xz_uniform : ∀ (S U : Set I), MeasurableSet S → MeasurableSet U →
    measure ((S ×ˢ Set.univ) ×ˢ U) = volume S * volume U
  yz_uniform : ∀ (T U : Set I), MeasurableSet T → MeasurableSet U →
    measure ((Set.univ ×ˢ T) ×ˢ U) = volume T * volume U

instance (W : LatinonMeasure) : IsProbabilityMeasure W.measure where
  measure_univ := by
    have h := W.xy_uniform Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa only [Set.univ_prod_univ,measure_univ,mul_one] using h

namespace LatinonMeasure

theorem xy_uniform_real (W : LatinonMeasure) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    W.measure.real ((S ×ˢ T) ×ˢ Set.univ) = volume.real S * volume.real T := by
  simp only [measureReal_def,W.xy_uniform S T hS hT,ENNReal.toReal_mul]

theorem xz_uniform_real (W : LatinonMeasure) (S U : Set I)
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    W.measure.real ((S ×ˢ Set.univ) ×ˢ U) = volume.real S * volume.real U := by
  simp only [measureReal_def,W.xz_uniform S U hS hU,ENNReal.toReal_mul]

theorem yz_uniform_real (W : LatinonMeasure) (T U : Set I)
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    W.measure.real ((Set.univ ×ˢ T) ×ˢ U) = volume.real T * volume.real U := by
  simp only [measureReal_def,W.yz_uniform T U hT hU,ENNReal.toReal_mul]

end LatinonMeasure

/-- A concrete inhabitant: the uniform Latinon with identity order map. -/
def uniformLatinonMeasure : LatinonMeasure where
  measure := ((volume : Measure I).prod volume).prod volume
  order := id
  order_preserving := MeasurePreserving.id volume
  xy_uniform := by
    intro S T _ _
    simp only [Measure.prod_prod,measure_univ,mul_one]
  xz_uniform := by
    intro S U _ _
    simp only [Measure.prod_prod,measure_univ,mul_one]
  yz_uniform := by
    intro T U _ _
    simp only [Measure.prod_prod,measure_univ,one_mul]

example : IsProbabilityMeasure uniformLatinonMeasure.measure := inferInstance

end LatinonEntropy

#print axioms LatinonEntropy.LatinonMeasure.xy_uniform_real
#print axioms LatinonEntropy.LatinonMeasure.xz_uniform_real
#print axioms LatinonEntropy.LatinonMeasure.yz_uniform_real
#print axioms LatinonEntropy.uniformLatinonMeasure
