module

public import LatinonConditionalSymbols

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal unitInterval

theorem latinonSymbolKernel_withDensity (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    unitSquareVolume.withDensity (fun p => latinonSymbolKernel W p U)=latinonSymbolSlice W U := by
  symm
  apply Measure.ext_prod
  intro S T hS hT
  rw [withDensity_apply _ (hS.prod hT),latinonSymbolKernel_rectangle W S T U hS hT hU]
  unfold latinonSymbolSlice
  rw [Measure.map_apply measurable_fst (hS.prod hT),
    Measure.restrict_apply ((hS.prod hT).preimage measurable_fst)]
  rfl

/-- The conditional symbol law agrees almost everywhere with the actual
Radon-Nikodym compression used in the cut metric. -/
theorem latinonSymbolKernel_ae_compression (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    (fun p => (latinonSymbolKernel W p).real U)=ᵐ[unitSquareVolume] latinonSymbolCompression W U := by
  have h := Measure.rnDeriv_withDensity unitSquareVolume (measurable_latinonSymbolKernel_event W U hU)
  rw [latinonSymbolKernel_withDensity W U hU] at h
  filter_upwards [h] with p hp
  exact (congrArg ENNReal.toReal hp).symm

theorem integrable_real_latinonSymbolKernel_event (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    Integrable (fun p => (latinonSymbolKernel W p).real U) unitSquareVolume := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_latinonSymbolKernel_event W U hU).ennreal_toReal.aemeasurable
  apply ae_of_all
  intro p
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have hcap : latinonSymbolKernel W p U ≤ 1 := by
    simpa only [measure_univ] using
      (measure_mono (Set.subset_univ U) : latinonSymbolKernel W p U ≤ latinonSymbolKernel W p Set.univ)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hcap

end LatinonEntropy

#print axioms LatinonEntropy.latinonSymbolKernel_withDensity
#print axioms LatinonEntropy.latinonSymbolKernel_ae_compression
#print axioms LatinonEntropy.integrable_real_latinonSymbolKernel_event
