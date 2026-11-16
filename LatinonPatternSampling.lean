module

public import FiniteIndependentKernel
public import LatinonConditionalSymbols
public import LatinOrderPatterns

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal unitInterval

abbrev LatinonPatternConfig (k l : ℕ) := (Fin k → I) × (Fin l → I)

def latinonPatternConfigLaw (k l : ℕ) : Measure (LatinonPatternConfig k l) :=
  (Measure.pi (fun _ : Fin k => (volume : Measure I))).prod
    (Measure.pi (fun _ : Fin l => (volume : Measure I)))

instance latinonPatternConfigLaw_probability (k l : ℕ) :
    IsProbabilityMeasure (latinonPatternConfigLaw k l) := by
  unfold latinonPatternConfigLaw
  infer_instance

def orderedLatinonPatternConfigs (W : LatinonMeasure) (k l : ℕ) :
    Set (LatinonPatternConfig k l) :=
  {c | StrictMono (W.order ∘ c.1) ∧ StrictMono (W.order ∘ c.2)}

theorem measurableSet_orderedLatinonPatternConfigs (W : LatinonMeasure) (k l : ℕ) :
    MeasurableSet (orderedLatinonPatternConfigs W k l) := by
  have hrow : MeasurableSet {c : LatinonPatternConfig k l | StrictMono (W.order ∘ c.1)} := by
    change MeasurableSet {c : LatinonPatternConfig k l |
      ∀ a b, a < b → W.order (c.1 a) < W.order (c.1 b)}
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun a => ?_)
    refine MeasurableSet.iInter (fun b => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
    have ha : Measurable (fun c : LatinonPatternConfig k l => W.order (c.1 a)) :=
      W.order_preserving.measurable.comp ((measurable_pi_apply a).comp measurable_fst)
    have hb : Measurable (fun c : LatinonPatternConfig k l => W.order (c.1 b)) :=
      W.order_preserving.measurable.comp ((measurable_pi_apply b).comp measurable_fst)
    exact measurableSet_lt ha hb
  have hcol : MeasurableSet {c : LatinonPatternConfig k l | StrictMono (W.order ∘ c.2)} := by
    change MeasurableSet {c : LatinonPatternConfig k l |
      ∀ a b, a < b → W.order (c.2 a) < W.order (c.2 b)}
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun a => ?_)
    refine MeasurableSet.iInter (fun b => ?_)
    refine MeasurableSet.iInter (fun _ => ?_)
    have ha : Measurable (fun c : LatinonPatternConfig k l => W.order (c.2 a)) :=
      W.order_preserving.measurable.comp ((measurable_pi_apply a).comp measurable_snd)
    have hb : Measurable (fun c : LatinonPatternConfig k l => W.order (c.2 b)) :=
      W.order_preserving.measurable.comp ((measurable_pi_apply b).comp measurable_snd)
    exact measurableSet_lt ha hb
  exact hrow.inter hcol

def latinonPatternCellKernel (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    Kernel (LatinonPatternConfig k l) I :=
  (latinonSymbolKernel W).comap (fun c => (c.1 a.1,c.2 a.2))
    (((measurable_pi_apply a.1).comp measurable_fst).prodMk
      ((measurable_pi_apply a.2).comp measurable_snd))

instance latinonPatternCellKernel_markov (W : LatinonMeasure) (k l : ℕ) (a : Fin k × Fin l) :
    IsMarkovKernel (latinonPatternCellKernel W k l a) := by
  unfold latinonPatternCellKernel
  infer_instance

def latinonPatternSymbolKernel (W : LatinonMeasure) (k l : ℕ) :
    Kernel (LatinonPatternConfig k l) ((Fin k × Fin l) → I) :=
  finiteIndependentKernel (latinonPatternCellKernel W k l)

instance latinonPatternSymbolKernel_markov (W : LatinonMeasure) (k l : ℕ) :
    IsMarkovKernel (latinonPatternSymbolKernel W k l) := by
  unfold latinonPatternSymbolKernel
  infer_instance

theorem latinonPatternSymbolKernel_rectangle (W : LatinonMeasure) (k l : ℕ)
    (c : LatinonPatternConfig k l) (U : (Fin k × Fin l) → Set I) :
    latinonPatternSymbolKernel W k l c (Set.pi Set.univ U)=
      ∏ a, latinonSymbolKernel W (c.1 a.1,c.2 a.2) (U a) := by
  rw [latinonPatternSymbolKernel,finiteIndependentKernel_rectangle]
  rfl

def unitOrderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → I) :=
  (fun v a => (v a : ℝ)) ⁻¹' orderPatternRealizations P

theorem measurableSet_unitOrderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    MeasurableSet (unitOrderPatternRealizations P) := by
  apply (measurableSet_orderPatternRealizations P).preimage
  exact measurable_pi_iff.mpr (fun a => measurable_subtype_coe.comp (measurable_pi_apply a))

def latinonPatternSampleLaw (W : LatinonMeasure) (k l : ℕ) :
    Measure (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  latinonPatternConfigLaw k l ⊗ₘ latinonPatternSymbolKernel W k l

instance latinonPatternSampleLaw_probability (W : LatinonMeasure) (k l : ℕ) :
    IsProbabilityMeasure (latinonPatternSampleLaw W k l) := by
  unfold latinonPatternSampleLaw
  infer_instance

def latinonPatternEvent {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) :
    Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
  orderedLatinonPatternConfigs W k l ×ˢ unitOrderPatternRealizations P

theorem measurableSet_latinonPatternEvent {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) : MeasurableSet (latinonPatternEvent W P) :=
  (measurableSet_orderedLatinonPatternConfigs W k l).prod (measurableSet_unitOrderPatternRealizations P)

/-- The ordered-sampling density, with the k! l! normalization of Garbe et al.
The conditional symbol laws are the actual disintegration of W.measure. -/
def latinonPatternDensity {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real (latinonPatternEvent W P)

theorem latinonPatternDensity_eq_setIntegral {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) :
    latinonPatternDensity W P=((k.factorial*l.factorial : ℕ) : ℝ)*
      ∫ c in orderedLatinonPatternConfigs W k l,
        (latinonPatternSymbolKernel W k l c).real (unitOrderPatternRealizations P)
          ∂latinonPatternConfigLaw k l := by
  have h := Measure.setIntegral_compProd
    (μ := latinonPatternConfigLaw k l) (κ := latinonPatternSymbolKernel W k l)
    (measurableSet_orderedLatinonPatternConfigs W k l) (measurableSet_unitOrderPatternRealizations P)
    (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  simpa only [latinonPatternDensity,latinonPatternSampleLaw,latinonPatternEvent,
    setIntegral_const,smul_eq_mul,mul_one] using
    congrArg (fun a : ℝ => ((k.factorial*l.factorial : ℕ) : ℝ)*a) h

theorem latinonPatternDensity_nonneg {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) : 0 ≤ latinonPatternDensity W P :=
  mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

theorem latinonPatternSampleLaw_ordered_univ (W : LatinonMeasure) (k l : ℕ) :
    (latinonPatternSampleLaw W k l).real (orderedLatinonPatternConfigs W k l ×ˢ Set.univ)=
      (latinonPatternConfigLaw k l).real (orderedLatinonPatternConfigs W k l) := by
  apply congrArg ENNReal.toReal
  rw [latinonPatternSampleLaw,Measure.compProd_apply_prod
    (measurableSet_orderedLatinonPatternConfigs W k l) MeasurableSet.univ]
  simp

theorem latinonPatternDensity_le_ordered_mass {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) : latinonPatternDensity W P ≤
      ((k.factorial*l.factorial : ℕ) : ℝ)*
        (latinonPatternConfigLaw k l).real (orderedLatinonPatternConfigs W k l) := by
  unfold latinonPatternDensity
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [← latinonPatternSampleLaw_ordered_univ W k l]
  exact measureReal_mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ _)) (measure_ne_top _ _)

end LatinonEntropy

#print axioms LatinonEntropy.latinonPatternConfigLaw_probability
#print axioms LatinonEntropy.measurableSet_orderedLatinonPatternConfigs
#print axioms LatinonEntropy.latinonPatternCellKernel_markov
#print axioms LatinonEntropy.latinonPatternSymbolKernel_markov
#print axioms LatinonEntropy.latinonPatternSymbolKernel_rectangle
#print axioms LatinonEntropy.measurableSet_unitOrderPatternRealizations
#print axioms LatinonEntropy.latinonPatternSampleLaw_probability
#print axioms LatinonEntropy.measurableSet_latinonPatternEvent
#print axioms LatinonEntropy.latinonPatternDensity_eq_setIntegral
#print axioms LatinonEntropy.latinonPatternDensity_nonneg
#print axioms LatinonEntropy.latinonPatternSampleLaw_ordered_univ
#print axioms LatinonEntropy.latinonPatternDensity_le_ordered_mass
