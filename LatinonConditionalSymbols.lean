module

public import LatinonSymbolCompression
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Disintegration.Integral

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal unitInterval

/-- The canonical conditional symbol law exists for all Latinons,
including those without a density with respect to three-dimensional volume. -/
def latinonSymbolKernel (W : LatinonMeasure) : Kernel (I × I) I := W.measure.condKernel

instance latinonSymbolKernel_markov (W : LatinonMeasure) : IsMarkovKernel (latinonSymbolKernel W) := by
  unfold latinonSymbolKernel
  infer_instance

theorem latinon_measure_fst (W : LatinonMeasure) : W.measure.fst=unitSquareVolume :=
  (latinon_xy_preserving W).map_eq

theorem latinonSymbolKernel_reconstruct (W : LatinonMeasure) :
    unitSquareVolume ⊗ₘ latinonSymbolKernel W=W.measure := by
  rw [← latinon_measure_fst W]
  exact W.measure.disintegrate W.measure.condKernel

theorem latinonSymbolKernel_rectangle (W : LatinonMeasure) (S T U : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (∫⁻ p in S ×ˢ T, latinonSymbolKernel W p U ∂unitSquareVolume)=
      W.measure ((S ×ˢ T) ×ˢ U) := by
  rw [← latinonSymbolKernel_reconstruct W,Measure.compProd_apply_prod (hS.prod hT) hU]

theorem measurable_latinonSymbolKernel_event (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) : Measurable (fun p => latinonSymbolKernel W p U) :=
  (latinonSymbolKernel W).measurable_coe hU

theorem latinonSymbolKernel_real_rectangle (W : LatinonMeasure) (S T U : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (∫ p in S ×ˢ T, (latinonSymbolKernel W p).real U ∂unitSquareVolume)=
      W.measure.real ((S ×ˢ T) ×ˢ U) := by
  have h := Measure.setIntegral_condKernel (ρ := W.measure) (hS.prod hT) hU
    (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  rw [latinon_measure_fst W] at h
  simpa only [latinonSymbolKernel,setIntegral_const,smul_eq_mul,mul_one] using h

end LatinonEntropy

#print axioms LatinonEntropy.latinonSymbolKernel_markov
#print axioms LatinonEntropy.latinon_measure_fst
#print axioms LatinonEntropy.latinonSymbolKernel_reconstruct
#print axioms LatinonEntropy.latinonSymbolKernel_rectangle
#print axioms LatinonEntropy.measurable_latinonSymbolKernel_event
#print axioms LatinonEntropy.latinonSymbolKernel_real_rectangle
