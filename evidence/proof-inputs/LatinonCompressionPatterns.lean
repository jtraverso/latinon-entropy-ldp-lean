module

public import LatinonSymbolPairs
public import LatinonCoarsePatterns
public import LatinonPatternNormalization

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def patternCompressionKernel {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :=
  patternEdgeKernel (latinonOrderKernel W) (latinonOrderKernel W)
    (fun a => latinonSymbolCompression W (lebesgueGridCell (b a)))

def coarsePatternDensity {k l : ℕ} (W : LatinonMeasure) (P : LatinOrderPattern k l) (q : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real
    (orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q)

def compressionPatternPolynomial {k l : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (q : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*∑ b ∈ patternBinAssignments P q,
    kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)

theorem patternCompressionKernel_measurable {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e : PatternVertex k l × PatternVertex k l) :
    Measurable (patternCompressionKernel W b e) :=
  patternEdgeKernel_measurable _ _ _ (latinonOrderKernel_measurable W)
    (latinonOrderKernel_measurable W) (fun _ => latinonSymbolCompression_measurable W _) e

theorem patternCompressionKernel_bounds {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e : PatternVertex k l × PatternVertex k l) :
    ∀ᵐ p ∂unitSquareVolume, patternCompressionKernel W b e p ∈ Set.Icc (0 : ℝ) 1 :=
  patternEdgeKernel_bounds _ _ _ (ae_of_all _ (latinonOrderKernel_bounds W))
    (ae_of_all _ (latinonOrderKernel_bounds W)) (fun _ => latinonSymbolCompression_bounds W _) e

theorem patternCompressionProduct_indicator {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (c : LatinonPatternConfig k l) :
    kernelGraphProduct (patternGraphEdges k l) (patternCompressionKernel W b) (patternConfigVertices c)=
      (orderedLatinonPatternConfigs W k l).indicator
        (fun c => ∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) c := by
  unfold patternCompressionKernel
  rw [patternGraphProduct_factor]
  change strictPairProduct (latinonOrderKernel W) c.1*strictPairProduct (latinonOrderKernel W) c.2*
    (∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2))=_
  rw [strictPairProduct_order,strictPairProduct_order]
  by_cases hr : StrictMono (W.order ∘ c.1) <;> by_cases hc : StrictMono (W.order ∘ c.2) <;>
    simp [orderedLatinonPatternConfigs,Set.indicator,hr,hc]

theorem patternSymbolRectangle_real {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (c : LatinonPatternConfig k l) :
    (latinonPatternSymbolKernel W k l c).real (patternBinRectangle b)=
      ∏ a : Fin k × Fin l, (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a)) := by
  have h := congrArg ENNReal.toReal (latinonPatternSymbolKernel_rectangle W k l c
    (fun a => lebesgueGridCell (b a)))
  simpa only [Measure.real,patternBinRectangle,ENNReal.toReal_prod] using h

theorem patternSymbolProduct_ae_compression {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :
    (fun c : LatinonPatternConfig k l => ∏ a : Fin k × Fin l,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a)))=ᵐ[latinonPatternConfigLaw k l]
    (fun c => ∏ a : Fin k × Fin l,
      latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) := by
  have hall : ∀ᵐ c ∂latinonPatternConfigLaw k l, ∀ a : Fin k × Fin l,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell (b a))=
        latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2) := by
    simp only [ae_all_iff]
    intro a
    have hm : MeasurePreserving (fun c : LatinonPatternConfig k l => (c.1 a.1,c.2 a.2))
        (latinonPatternConfigLaw k l) unitSquareVolume :=
      (vertexPair_preserving (.inl a.1 : PatternVertex k l) (.inr a.2) (by simp)).comp
        (patternConfigVertices_preserving k l)
    exact hm.quasiMeasurePreserving.ae
      (latinonSymbolKernel_ae_compression W _ (lebesgueGridCell_measurable (b a)))
  filter_upwards [hall] with c hc
  exact Finset.prod_congr rfl (fun a _ => hc a)

theorem orderedPatternBin_event_eq_graphDensity {k l q : ℕ} (W : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) :
    (latinonPatternSampleLaw W k l).real
      (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b)=
        kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b) := by
  have he := Measure.setIntegral_compProd
    (μ := latinonPatternConfigLaw k l) (κ := latinonPatternSymbolKernel W k l)
    (measurableSet_orderedLatinonPatternConfigs W k l) (measurableSet_patternBinRectangle b)
    (f := fun _ => (1 : ℝ)) (integrable_const 1).integrableOn
  have hreal : (latinonPatternSampleLaw W k l).real
      (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b)=
        ∫ c in orderedLatinonPatternConfigs W k l,
          (latinonPatternSymbolKernel W k l c).real (patternBinRectangle b) ∂latinonPatternConfigLaw k l := by
    simpa only [latinonPatternSampleLaw,setIntegral_const,smul_eq_mul,mul_one] using he
  rw [hreal]
  simp_rw [patternSymbolRectangle_real]
  calc
    _ = ∫ c in orderedLatinonPatternConfigs W k l,
        ∏ a : Fin k × Fin l, latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)
          ∂latinonPatternConfigLaw k l :=
      integral_congr_ae (ae_restrict_of_ae (patternSymbolProduct_ae_compression W b))
    _ = ∫ c, (orderedLatinonPatternConfigs W k l).indicator
        (fun c => ∏ a : Fin k × Fin l,
          latinonSymbolCompression W (lebesgueGridCell (b a)) (c.1 a.1,c.2 a.2)) c
          ∂latinonPatternConfigLaw k l :=
      (integral_indicator (measurableSet_orderedLatinonPatternConfigs W k l)).symm
    _ = ∫ c, kernelGraphProduct (patternGraphEdges k l) (patternCompressionKernel W b)
        (patternConfigVertices c) ∂latinonPatternConfigLaw k l :=
      integral_congr_ae (ae_of_all _ (fun c => (patternCompressionProduct_indicator W b c).symm))
    _ = _ := integral_patternConfigVertices k l _

/-- The approximation is an actual probability of the actual conditional
symbol sampling, represented by a finite polynomial of cut compressions. -/
theorem coarsePatternDensity_eq_polynomial {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternDensity W P q=compressionPatternPolynomial W P q := by
  unfold coarsePatternDensity compressionPatternPolynomial
  congr 1
  have he : orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q=
      ⋃ b ∈ patternBinAssignments P q, orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b := by
    ext p
    simp only [coarsePatternRealizations,Set.mem_prod,Set.mem_iUnion]
    aesop
  rw [he]
  calc
    _ = ∑ b ∈ patternBinAssignments P q, (latinonPatternSampleLaw W k l).real
        (orderedLatinonPatternConfigs W k l ×ˢ patternBinRectangle b) := by
      apply measureReal_biUnion_finset
      · intro b _ c _ hbc
        apply Set.disjoint_left.mpr
        intro p hb hc
        exact Set.disjoint_left.mp (patternBinRectangle_disjoint hq b c hbc) hb.2 hc.2
      · intro b _
        exact (measurableSet_orderedLatinonPatternConfigs W k l).prod (measurableSet_patternBinRectangle b)
      · intro b _
        exact measure_ne_top _ _
    _ = _ := Finset.sum_congr rfl (fun b _ => orderedPatternBin_event_eq_graphDensity W b)

end LatinonEntropy

#print axioms LatinonEntropy.patternCompressionKernel_measurable
#print axioms LatinonEntropy.patternCompressionKernel_bounds
#print axioms LatinonEntropy.patternCompressionProduct_indicator
#print axioms LatinonEntropy.patternSymbolRectangle_real
#print axioms LatinonEntropy.patternSymbolProduct_ae_compression
#print axioms LatinonEntropy.orderedPatternBin_event_eq_graphDensity
#print axioms LatinonEntropy.coarsePatternDensity_eq_polynomial
