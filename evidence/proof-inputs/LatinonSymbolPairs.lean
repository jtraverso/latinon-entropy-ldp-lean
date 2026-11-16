module

public import LatinonSymbolAverages
public import VertexLeafIntegration
public import LatinonPatternGraph

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical unitInterval

theorem integral_patternConfigVertices (k l : ℕ) (F : (PatternVertex k l → I) → ℝ) :
    (∫ c, F (patternConfigVertices c) ∂latinonPatternConfigLaw k l)=
      ∫ x, F x ∂vertexSampleLaw (PatternVertex k l) :=
  (patternConfigVertices_preserving k l).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : PatternVertex k l => I)).symm.measurableEmbedding F

/-- Two distinct cells have independent uniform symbols before ordering
the sampled row/column coordinates. Shared rows and columns are allowed. -/
theorem latinonSymbolPair_integral (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) (U T : Set I)
    (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (∫ c, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U*
      (latinonSymbolKernel W (c.1 b.1,c.2 b.2)).real T ∂latinonPatternConfigLaw k l)=
      (volume : Measure I).real U*(volume : Measure I).real T := by
  let f : I × I → ℝ := fun p => (latinonSymbolKernel W p).real U
  let g : I × I → ℝ := fun p => (latinonSymbolKernel W p).real T
  have hfm : Measurable f := (measurable_latinonSymbolKernel_event W U hU).ennreal_toReal
  have hgm : Measurable g := (measurable_latinonSymbolKernel_event W T hT).ennreal_toReal
  have hfb : ∀ p, f p ∈ Set.Icc (0 : ℝ) 1 := latinonSymbolKernel_real_mem_Icc W U
  have hgb : ∀ p, g p ∈ Set.Icc (0 : ℝ) 1 := latinonSymbolKernel_real_mem_Icc W T
  have htotal : (∫ x : PatternVertex k l → I, g (x (.inl b.1),x (.inr b.2))
      ∂vertexSampleLaw (PatternVertex k l))=(volume : Measure I).real T := by
    rw [integral_vertexPair (Sum.inl b.1 : PatternVertex k l) (Sum.inr b.2) (by simp)
      g (integrable_real_latinonSymbolKernel_event W T hT)]
    exact latinonSymbolKernel_mean W T hT
  change (∫ c, f (c.1 a.1,c.2 a.2)*g (c.1 b.1,c.2 b.2) ∂latinonPatternConfigLaw k l)=_
  have he := integral_patternConfigVertices k l
    (fun x => f (x (.inl a.1),x (.inr a.2))*g (x (.inl b.1),x (.inr b.2)))
  change (∫ c, f (c.1 a.1,c.2 a.2)*g (c.1 b.1,c.2 b.2) ∂latinonPatternConfigLaw k l)=_ at he
  rw [he]
  by_cases hr : a.1=b.1
  · have hc : b.2 ≠ a.2 := fun h => hab (Prod.ext hr h.symm)
    have h := integral_vertex_leaf
      (Sum.inr a.2 : PatternVertex k l) (.inl a.1) (.inl b.1) (.inr b.2)
      (by simp) (by simp) (by simpa using hc)
      (fun p => f p.swap) g (hfm.comp measurable_swap) hgm
      (fun p => hfb p.swap) hgb ((volume : Measure I).real U)
      (latinonSymbolKernel_row_mean W U hU)
    change (∫ x : PatternVertex k l → I, f (x (.inl a.1),x (.inr a.2))*
      g (x (.inl b.1),x (.inr b.2)) ∂vertexSampleLaw (PatternVertex k l))=_ at h
    rw [h,htotal]
  · have h := integral_vertex_leaf
      (Sum.inl a.1 : PatternVertex k l) (.inr a.2) (.inl b.1) (.inr b.2)
      (by simp) (by simpa using Ne.symm hr) (by simp)
      f g hfm hgm hfb hgb ((volume : Measure I).real U)
      (latinonSymbolKernel_col_mean W U hU)
    rw [h,htotal]

theorem latinonPatternSampleLaw_symbol_event_real (W : LatinonMeasure) (k l : ℕ)
    (E : Set ((Fin k × Fin l) → I)) (hE : MeasurableSet E) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ E)=
      ∫ c, (latinonPatternSymbolKernel W k l c).real E ∂latinonPatternConfigLaw k l := by
  have h := Measure.setIntegral_compProd
    (μ := latinonPatternConfigLaw k l) (κ := latinonPatternSymbolKernel W k l)
    MeasurableSet.univ hE (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  simpa only [latinonPatternSampleLaw,setIntegral_const,smul_eq_mul,mul_one,
    Measure.restrict_univ] using h

theorem latinonPatternSymbolKernel_pair_event (W : LatinonMeasure) {k l : ℕ}
    (c : LatinonPatternConfig k l) (a b : Fin k × Fin l) (hab : a ≠ b)
    (U T : Set I) (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (latinonPatternSymbolKernel W k l c) {z | z a ∈ U ∧ z b ∈ T}=
      latinonSymbolKernel W (c.1 a.1,c.2 a.2) U*
        latinonSymbolKernel W (c.1 b.1,c.2 b.2) T := by
  let μ := fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)
  have hind := (iIndepFun_pi (μ := μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun hab
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable
  rw [(measurePreserving_eval μ a).map_eq,(measurePreserving_eval μ b).map_eq] at hmap
  have h := congrArg (fun m : Measure (I × I) => m (U ×ˢ T)) hmap
  rw [Measure.map_apply ((measurable_pi_apply a).prodMk (measurable_pi_apply b)) (hU.prod hT),
    Measure.prod_prod] at h
  exact h

theorem latinonPatternSampleLaw_pair_event_real (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) (U T : Set I)
    (hU : MeasurableSet U) (hT : MeasurableSet T) :
    (latinonPatternSampleLaw W k l).real
      (Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T})=
        (volume : Measure I).real U*(volume : Measure I).real T := by
  have hE : MeasurableSet {z : (Fin k × Fin l) → I | z a ∈ U ∧ z b ∈ T} :=
    (hU.preimage (measurable_pi_apply a)).inter (hT.preimage (measurable_pi_apply b))
  rw [latinonPatternSampleLaw_symbol_event_real W k l
    {z : (Fin k × Fin l) → I | z a ∈ U ∧ z b ∈ T} hE]
  have hpoint (c : LatinonPatternConfig k l) :
      (latinonPatternSymbolKernel W k l c).real {z | z a ∈ U ∧ z b ∈ T}=
        (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U*
          (latinonSymbolKernel W (c.1 b.1,c.2 b.2)).real T := by
    exact (congrArg ENNReal.toReal (latinonPatternSymbolKernel_pair_event W c a b hab U T hU hT)).trans
      (ENNReal.toReal_mul)
  simp_rw [hpoint]
  exact latinonSymbolPair_integral W a b hab U T hU hT

theorem latinonPatternSampleLaw_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (a b : Fin k × Fin l) (hab : a ≠ b) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b))
      (latinonPatternSampleLaw W k l) unitSquareVolume := by
  have hm : Measurable (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) :=
    ((measurable_pi_apply a).comp measurable_snd).prodMk ((measurable_pi_apply b).comp measurable_snd)
  refine ⟨hm,?_⟩
  apply Measure.ext_prod
  intro U T hU hT
  have hset : (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) ⁻¹'
      (U ×ˢ T)=Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq]
  rw [Measure.map_apply hm (hU.prod hT),hset]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ {z | z a ∈ U ∧ z b ∈ T})=
    unitSquareVolume.real (U ×ˢ T)
  rw [latinonPatternSampleLaw_pair_event_real W a b hab U T hU hT,measureReal_prod_prod]

theorem latinonPatternSampleLaw_single_event_real (W : LatinonMeasure) {k l : ℕ}
    (a : Fin k × Fin l) (U : Set I) (hU : MeasurableSet U) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ {z | z a ∈ U})=
      (volume : Measure I).real U := by
  have hE : MeasurableSet {z : (Fin k × Fin l) → I | z a ∈ U} := hU.preimage (measurable_pi_apply a)
  rw [latinonPatternSampleLaw_symbol_event_real W k l {z : (Fin k × Fin l) → I | z a ∈ U} hE]
  have hpoint (c : LatinonPatternConfig k l) :
      (latinonPatternSymbolKernel W k l c).real {z | z a ∈ U}=
        (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U := by
    have hm : MeasurePreserving (fun z : (Fin k × Fin l) → I => z a)
        (latinonPatternSymbolKernel W k l c) (latinonSymbolKernel W (c.1 a.1,c.2 a.2)) :=
      measurePreserving_eval (fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)) a
    exact congrArg ENNReal.toReal (hm.measure_preimage hU.nullMeasurableSet)
  simp_rw [hpoint]
  have he := integral_patternConfigVertices k l
    (fun x => (latinonSymbolKernel W (x (.inl a.1),x (.inr a.2))).real U)
  change (∫ c, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real U ∂latinonPatternConfigLaw k l)=_ at he
  rw [he,integral_vertexPair (Sum.inl a.1 : PatternVertex k l) (Sum.inr a.2) (by simp)
    _ (integrable_real_latinonSymbolKernel_event W U hU)]
  exact latinonSymbolKernel_mean W U hU

theorem latinonPatternSampleLaw_single_preserving (W : LatinonMeasure) {k l : ℕ}
    (a : Fin k × Fin l) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a)
      (latinonPatternSampleLaw W k l) (volume : Measure I) := by
  have hm : Measurable (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a) :=
    (measurable_pi_apply a).comp measurable_snd
  refine ⟨hm,?_⟩
  apply Measure.ext
  intro U hU
  have hset : (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => p.2 a) ⁻¹' U=
      Set.univ ×ˢ {z | z a ∈ U} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq]
  rw [Measure.map_apply hm hU,hset]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  exact latinonPatternSampleLaw_single_event_real W a U hU

end LatinonEntropy

#print axioms LatinonEntropy.integral_patternConfigVertices
#print axioms LatinonEntropy.latinonSymbolPair_integral
#print axioms LatinonEntropy.latinonPatternSampleLaw_symbol_event_real
#print axioms LatinonEntropy.latinonPatternSymbolKernel_pair_event
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_event_real
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_single_event_real
#print axioms LatinonEntropy.latinonPatternSampleLaw_single_preserving
