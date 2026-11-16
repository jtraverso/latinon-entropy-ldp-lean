module

public import LatinonCutInvariance
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Data.EReal.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval ENNReal

/-- The rate retains infinite divergence, including singular Latinons. -/
def latinonRate (W : LatinonMeasure) : ℝ≥0∞ :=
  InformationTheory.klDiv W.measure uniformLatinonMeasure.measure

/-- Entropy is minus relative entropy, with value -infinity allowed. -/
def latinonEntropy (W : LatinonMeasure) : EReal := -(latinonRate W : EReal)

theorem latinonRate_uniform : latinonRate uniformLatinonMeasure = 0 :=
  InformationTheory.klDiv_self _

theorem latinonRate_eq_zero_iff (W : LatinonMeasure) :
    latinonRate W = 0 ↔ W.measure = uniformLatinonMeasure.measure :=
  InformationTheory.klDiv_eq_zero_iff

theorem latinonEntropy_nonpos (W : LatinonMeasure) : latinonEntropy W ≤ 0 := by
  have h : (0 : EReal) ≤ (latinonRate W : EReal) := by
    exact_mod_cast (bot_le : (0 : ℝ≥0∞) ≤ latinonRate W)
  exact EReal.neg_le_zero.mpr h

theorem latinonEntropy_uniform : latinonEntropy uniformLatinonMeasure = 0 := by
  simp only [latinonEntropy,latinonRate_uniform,EReal.coe_ennreal_zero,neg_zero]

theorem latinonEntropy_eq_bot_iff (W : LatinonMeasure) :
    latinonEntropy W = ⊥ ↔ latinonRate W = ⊤ := by
  change -(latinonRate W : EReal) = ⊥ ↔ _
  rw [neg_eq_iff_eq_neg]
  simp

theorem relabel_uniform_latinon_measure (e f : LatinonRelabel) :
    relabelLatinonMeasure uniformLatinonMeasure.measure e f = uniformLatinonMeasure.measure := by
  apply Measure.ext_prod₃'
  intro S T U hS hT hU
  rw [relabelLatinonMeasure_box _ e f S T U hS hT hU]
  change (((volume : Measure I).prod volume).prod volume)
      (((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T)) ×ˢ U) =
    (((volume : Measure I).prod volume).prod volume) ((S ×ˢ T) ×ˢ U)
  rw [Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,
    e.symm.preserves.measure_preimage hS.nullMeasurableSet,
    f.symm.preserves.measure_preimage hT.nullMeasurableSet]

/-- Two inverse data-processing inequalities give exact invariance. -/
theorem latinon_measure_rate_relabel (W : LatinonMeasure) (e f : LatinonRelabel) :
    InformationTheory.klDiv (relabelLatinonMeasure W.measure e f) uniformLatinonMeasure.measure =
      latinonRate W := by
  have hl := InformationTheory.klDiv_map_le (μ := W.measure) (ν := uniformLatinonMeasure.measure)
    (inverseCoordinateRelabel_measurable e f)
  change InformationTheory.klDiv (relabelLatinonMeasure W.measure e f)
    (relabelLatinonMeasure uniformLatinonMeasure.measure e f) ≤ latinonRate W at hl
  rw [relabel_uniform_latinon_measure] at hl
  have hr := InformationTheory.klDiv_map_le (μ := relabelLatinonMeasure W.measure e f)
    (ν := uniformLatinonMeasure.measure) (inverseCoordinateRelabel_measurable e.symm f.symm)
  change InformationTheory.klDiv
    (relabelLatinonMeasure (relabelLatinonMeasure W.measure e f) e.symm f.symm)
    (relabelLatinonMeasure uniformLatinonMeasure.measure e.symm f.symm) ≤ _ at hr
  rw [relabelLatinonMeasure_inverse,relabel_uniform_latinon_measure] at hr
  exact le_antisymm hl hr

end LatinonEntropy

#print axioms LatinonEntropy.latinonRate_uniform
#print axioms LatinonEntropy.latinonRate_eq_zero_iff
#print axioms LatinonEntropy.latinonEntropy_nonpos
#print axioms LatinonEntropy.latinonEntropy_uniform
#print axioms LatinonEntropy.latinonEntropy_eq_bot_iff
#print axioms LatinonEntropy.relabel_uniform_latinon_measure
#print axioms LatinonEntropy.latinon_measure_rate_relabel
