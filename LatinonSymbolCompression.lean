module

public import LatinonMeasureSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev unitSquareVolume : Measure (I × I) := (volume : Measure I).prod volume

theorem latinon_xy_preserving (W : LatinonMeasure) :
    MeasurePreserving (Prod.fst : LatinonPoint → I × I) W.measure unitSquareVolume := by
  refine ⟨measurable_fst,?_⟩
  apply Measure.ext_prod
  intro S T hS hT
  rw [Measure.map_apply measurable_fst (hS.prod hT),Measure.prod_prod]
  have he : (Prod.fst : LatinonPoint → I × I) ⁻¹' (S ×ˢ T) = (S ×ˢ T) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  rw [he,W.xy_uniform S T hS hT]

/-- Actual two-dimensional symbol slice,defined for arbitrary Latinons,
including singular ones. Only the xy marginal is used for domination. -/
def latinonSymbolSlice (W : LatinonMeasure) (U : Set I) : Measure (I × I) :=
  (W.measure.restrict ((Prod.snd : LatinonPoint → I) ⁻¹' U)).map Prod.fst

instance (W : LatinonMeasure) (U : Set I) : IsFiniteMeasure (latinonSymbolSlice W U) := by
  unfold latinonSymbolSlice
  infer_instance

theorem latinonSymbolSlice_le (W : LatinonMeasure) (U : Set I) :
    latinonSymbolSlice W U ≤ unitSquareVolume := by
  have h := Measure.map_mono
    (Measure.restrict_le_self : W.measure.restrict ((Prod.snd : LatinonPoint → I) ⁻¹' U) ≤ W.measure)
    (measurable_fst : Measurable (Prod.fst : LatinonPoint → I × I))
  exact h.trans_eq (latinon_xy_preserving W).map_eq

theorem latinonSymbolSlice_ac (W : LatinonMeasure) (U : Set I) :
    latinonSymbolSlice W U ≪ unitSquareVolume := by
  intro E hE
  exact le_zero_iff.mp (((latinonSymbolSlice_le W U) E).trans_eq hE)

def latinonSymbolCompression (W : LatinonMeasure) (U : Set I) (p : I × I) : ℝ :=
  ((latinonSymbolSlice W U).rnDeriv unitSquareVolume p).toReal

theorem latinonSymbolCompression_measurable (W : LatinonMeasure) (U : Set I) :
    Measurable (latinonSymbolCompression W U) :=
  (Measure.measurable_rnDeriv (latinonSymbolSlice W U) unitSquareVolume).ennreal_toReal

theorem latinonSymbolCompression_integrable (W : LatinonMeasure) (U : Set I) :
    Integrable (latinonSymbolCompression W U) unitSquareVolume :=
  Measure.integrable_toReal_rnDeriv

theorem latinonSymbolCompression_bounds (W : LatinonMeasure) (U : Set I) :
    ∀ᵐ p ∂unitSquareVolume, latinonSymbolCompression W U p ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (latinonSymbolSlice_le W U)] with p hp
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  simpa only [latinonSymbolCompression,ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top hp

theorem latinonSymbolSlice_rectangle (W : LatinonMeasure) (U S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (latinonSymbolSlice W U).real (S ×ˢ T) = W.measure.real ((S ×ˢ T) ×ˢ U) := by
  apply congrArg ENNReal.toReal
  rw [latinonSymbolSlice,Measure.map_apply measurable_fst (hS.prod hT),
    Measure.restrict_apply ((hS.prod hT).preimage measurable_fst)]
  congr 1

/-- Exact recovery of every symbol-slice rectangle from its bounded
compression; no density or finite-KL assumption on W is supplied. -/
theorem latinonSymbolCompression_rectangle (W : LatinonMeasure) (U S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ p in S ×ˢ T, latinonSymbolCompression W U p ∂unitSquareVolume) =
      W.measure.real ((S ×ˢ T) ×ˢ U) := by
  exact (Measure.setIntegral_toReal_rnDeriv (latinonSymbolSlice_ac W U) (S ×ˢ T)).trans
    (latinonSymbolSlice_rectangle W U S T hS hT)

end LatinonEntropy

#print axioms LatinonEntropy.latinon_xy_preserving
#print axioms LatinonEntropy.latinonSymbolSlice_le
#print axioms LatinonEntropy.latinonSymbolSlice_ac
#print axioms LatinonEntropy.latinonSymbolCompression_measurable
#print axioms LatinonEntropy.latinonSymbolCompression_integrable
#print axioms LatinonEntropy.latinonSymbolCompression_bounds
#print axioms LatinonEntropy.latinonSymbolSlice_rectangle
#print axioms LatinonEntropy.latinonSymbolCompression_rectangle
