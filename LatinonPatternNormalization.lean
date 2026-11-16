module

public import LatinonPatternSampling
public import OrderedTupleNormalization

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal unitInterval

theorem orderedLatinonPatternConfigs_normalization (W : LatinonMeasure) (k l : ℕ) :
    ((k.factorial*l.factorial : ℕ) : ℝ)*
      (latinonPatternConfigLaw k l).real (orderedLatinonPatternConfigs W k l)=1 := by
  have hset : orderedLatinonPatternConfigs W k l=
      {x : Fin k → I | StrictMono (W.order ∘ x)} ×ˢ
        {y : Fin l → I | StrictMono (W.order ∘ y)} := rfl
  rw [hset,latinonPatternConfigLaw,measureReal_prod_prod,Nat.cast_mul]
  change (k.factorial : ℝ)*(l.factorial : ℝ)*
    ((unitTupleLaw k).real {x | StrictMono (W.order ∘ x)}*
      (unitTupleLaw l).real {y | StrictMono (W.order ∘ y)})=1
  calc
    _ = ((k.factorial : ℝ)*(unitTupleLaw k).real {x | StrictMono (W.order ∘ x)})*
        ((l.factorial : ℝ)*(unitTupleLaw l).real {y | StrictMono (W.order ∘ y)}) := by ring
    _ = 1 := by
      rw [unitTupleLaw_order_preserving_normalization k W.order W.order_preserving,
        unitTupleLaw_order_preserving_normalization l W.order W.order_preserving,one_mul]

def orderedLatinonPatternConfigLaw (W : LatinonMeasure) (k l : ℕ) :
    Measure (LatinonPatternConfig k l) :=
  ENNReal.ofReal ((k.factorial*l.factorial : ℕ) : ℝ) •
    (latinonPatternConfigLaw k l).restrict (orderedLatinonPatternConfigs W k l)

instance orderedLatinonPatternConfigLaw_probability (W : LatinonMeasure) (k l : ℕ) :
    IsProbabilityMeasure (orderedLatinonPatternConfigLaw W k l) := by
  refine ⟨?_⟩
  rw [orderedLatinonPatternConfigLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  rw [← ENNReal.ofReal_toReal
    (measure_ne_top (latinonPatternConfigLaw k l) (orderedLatinonPatternConfigs W k l))]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  change ENNReal.ofReal (((k.factorial*l.factorial : ℕ) : ℝ)*
    (latinonPatternConfigLaw k l).real (orderedLatinonPatternConfigs W k l))=1
  rw [orderedLatinonPatternConfigs_normalization,ENNReal.ofReal_one]

def orderedLatinonPatternSampleLaw (W : LatinonMeasure) (k l : ℕ) :
    Measure (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  orderedLatinonPatternConfigLaw W k l ⊗ₘ latinonPatternSymbolKernel W k l

instance orderedLatinonPatternSampleLaw_probability (W : LatinonMeasure) (k l : ℕ) :
    IsProbabilityMeasure (orderedLatinonPatternSampleLaw W k l) := by
  unfold orderedLatinonPatternSampleLaw
  infer_instance

/-- The factorial-normalized integral is exactly a probability under
ordered row/column sampling followed by conditionally independent symbols. -/
theorem latinonPatternDensity_eq_orderedSampleLaw {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) : latinonPatternDensity W P=
      (orderedLatinonPatternSampleLaw W k l).real (Set.univ ×ˢ unitOrderPatternRealizations P) := by
  symm
  unfold orderedLatinonPatternSampleLaw Measure.real
  rw [Measure.compProd_apply_prod MeasurableSet.univ (measurableSet_unitOrderPatternRealizations P)]
  simp only [Measure.restrict_univ]
  rw [orderedLatinonPatternConfigLaw,lintegral_smul_measure]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
  rw [← Measure.compProd_apply_prod (measurableSet_orderedLatinonPatternConfigs W k l)
    (measurableSet_unitOrderPatternRealizations P)]
  rfl

theorem latinonPatternDensity_mem_Icc {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) : latinonPatternDensity W P ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨latinonPatternDensity_nonneg W P,?_⟩
  exact (latinonPatternDensity_le_ordered_mass W P).trans
    (orderedLatinonPatternConfigs_normalization W k l).le

end LatinonEntropy

#print axioms LatinonEntropy.orderedLatinonPatternConfigs_normalization
#print axioms LatinonEntropy.orderedLatinonPatternConfigLaw_probability
#print axioms LatinonEntropy.orderedLatinonPatternSampleLaw_probability
#print axioms LatinonEntropy.latinonPatternDensity_eq_orderedSampleLaw
#print axioms LatinonEntropy.latinonPatternDensity_mem_Icc
