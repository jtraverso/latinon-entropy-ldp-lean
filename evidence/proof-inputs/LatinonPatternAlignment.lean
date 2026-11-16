module

public import LatinonCompressionPatterns
public import LatinonPseudometric

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinon_symbol_two_relabel_rectangle_integral (W : LatinonMeasure) (e f : LatinonRelabel)
    (U S T : Set I) (hU : MeasurableSet U) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (relabelLatinonMeasure W.measure e f).real ((S ×ˢ T) ×ˢ U)=
      ∫ p in S ×ˢ T, latinonSymbolCompression W U (e p.1,f p.2) ∂unitSquareVolume := by
  let ep : (I × I) ≃ᵐ (I × I) := e.equiv.prodCongr f.equiv
  have hm : MeasurePreserving ep unitSquareVolume unitSquareVolume := e.preserves.prod f.preserves
  have hset : ep ⁻¹' ((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T))=S ×ˢ T := by
    ext p
    change (e.symm (e p.1) ∈ S ∧ f.symm (f p.2) ∈ T) ↔ (p.1 ∈ S ∧ p.2 ∈ T)
    rw [e.symm_apply_apply,f.symm_apply_apply]
  have he := hm.setIntegral_preimage_emb ep.measurableEmbedding (latinonSymbolCompression W U)
    ((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T))
  rw [hset] at he
  rw [relabelLatinonMeasure_real_box _ e f S T U hS hT hU,
    ← latinonSymbolCompression_rectangle W U _ _ (hS.preimage e.symm.measurable) (hT.preimage f.symm.measurable)]
  exact he.symm

theorem latinon_order_relabel_rectangle_integral (W : LatinonMeasure) (e : LatinonRelabel)
    (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ p in S ×ˢ T, latinonOrderKernel W (e p.1,e p.2) ∂unitSquareVolume)=
      orderBox (W.order ∘ e) ⟨S,T,hS,hT⟩ := by
  change (∫ p in S ×ˢ T, (orderRelation (W.order ∘ e)).indicator (fun _ => (1 : ℝ)) p
    ∂unitSquareVolume)=_
  rw [setIntegral_indicator (orderRelation_measurable _ (W.order_preserving.measurable.comp e.measurable)),
    setIntegral_const,smul_eq_mul,mul_one]
  rfl

theorem orderKernel_alignment_cut (W V : LatinonMeasure) (e : LatinonRelabel) :
    KernelCutClose (latinonOrderKernel W) (fun p => latinonOrderKernel V (e p.1,e p.2))
      (orderCut W.order (V.order ∘ e)) := by
  intro S T hS hT
  have hi : Integrable (fun p : I × I => latinonOrderKernel V (e p.1,e p.2)) unitSquareVolume :=
    (e.preserves.prod e.preserves).integrable_comp_of_integrable (latinonOrderKernel_integrable V)
  rw [integral_sub (latinonOrderKernel_integrable W).integrableOn hi.integrableOn,
    ← orderBox_eq_orderKernel_integral W ⟨S,T,hS,hT⟩,
    latinon_order_relabel_rectangle_integral V e S T hS hT]
  exact orderCut_test_le W.order (V.order ∘ e) ⟨S,T,hS,hT⟩

theorem symbolGridKernel_alignment_cut (W V : LatinonMeasure) (e f : LatinonRelabel)
    {q : ℕ} (j : Fin q) :
    KernelCutClose (latinonSymbolCompression W (lebesgueGridCell j))
      (fun p => latinonSymbolCompression V (lebesgueGridCell j) (e p.1,f p.2))
      (measureCut W.measure (relabelLatinonMeasure V.measure e f)) := by
  intro S T hS hT
  have hi : Integrable (fun p : I × I => latinonSymbolCompression V (lebesgueGridCell j) (e p.1,f p.2))
      unitSquareVolume := (e.preserves.prod f.preserves).integrable_comp_of_integrable
        (latinonSymbolCompression_integrable V (lebesgueGridCell j))
  rw [integral_sub (latinonSymbolCompression_integrable W _).integrableOn hi.integrableOn,
    latinonSymbolCompression_rectangle W _ S T hS hT,
    ← latinon_symbol_two_relabel_rectangle_integral V e f _ S T (lebesgueGridCell_measurable j) hS hT]
  exact measureCut_test_le W.measure (relabelLatinonMeasure V.measure e f)
    { rows := S,cols := T,rows_measurable := hS,cols_measurable := hT,
      symbols := lebesgueGridCell j,symbols_measurable := lebesgueGridCell_measurable j,
      symbols_interval := Set.ordConnected_Ioc.preimage_mono (fun _ _ h => h) }

def patternVertexRelabel {k l : ℕ} (e f : LatinonRelabel) (v : PatternVertex k l) : I → I :=
  Sum.elim (fun _ => e) (fun _ => f) v

theorem patternVertexRelabel_preserving {k l : ℕ} (e f : LatinonRelabel) (v : PatternVertex k l) :
    MeasurePreserving (patternVertexRelabel e f v) volume volume := by
  cases v
  · exact e.preserves
  · exact f.preserves

theorem patternCompressionKernel_alignment_cut {k l q : ℕ} (W V : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e f : LatinonRelabel) (a : PatternVertex k l × PatternVertex k l) :
    KernelCutClose (patternCompressionKernel W b a)
      (fun p => patternCompressionKernel V b a
        (patternVertexRelabel e f a.1 p.1,patternVertexRelabel e f a.2 p.2))
      (latinonAlignmentCost W V e f) := by
  obtain ⟨u,v⟩ := a
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      exact fun S T hS hT => ((orderKernel_alignment_cut W V e) S T hS hT).trans
        (row_orderCut_le_alignmentCost W V e f)
    | inr j =>
      exact fun S T hS hT => ((symbolGridKernel_alignment_cut W V e f (b (i,j))) S T hS hT).trans
        (measureCut_le_alignmentCost W V e f)
  | inr i =>
    cases v with
    | inl j =>
      intro S T _ _
      simpa only [patternCompressionKernel,patternEdgeKernel,sub_self,integral_zero,abs_zero] using
        latinonAlignmentCost_nonneg W V e f
    | inr j =>
      exact fun S T hS hT => ((orderKernel_alignment_cut W V f) S T hS hT).trans
        (col_orderCut_le_alignmentCost W V e f)

theorem patternCompressionGraph_alignment {k l q : ℕ} (W V : LatinonMeasure)
    (b : (Fin k × Fin l) → Fin q) (e f : LatinonRelabel) :
    |kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)-
      kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel V b)| ≤
        ((patternGraphEdges k l).card : ℝ)*latinonAlignmentCost W V e f := by
  let ρ := patternVertexRelabel (k := k) (l := l) e f
  have hm (a : PatternVertex k l × PatternVertex k l) :
      Measurable (fun p : I × I => patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2)) :=
    (patternCompressionKernel_measurable V b a).comp
      (((patternVertexRelabel_preserving e f a.1).measurable.comp measurable_fst).prodMk
        ((patternVertexRelabel_preserving e f a.2).measurable.comp measurable_snd))
  have hb (a : PatternVertex k l × PatternVertex k l) :
      ∀ᵐ p ∂unitSquareVolume, patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2) ∈ Set.Icc (0 : ℝ) 1 :=
    ((patternVertexRelabel_preserving e f a.1).prod (patternVertexRelabel_preserving e f a.2)).quasiMeasurePreserving.ae
      (patternCompressionKernel_bounds V b a)
  have h := kernelGraphDensity_counting_ae (patternGraphEdges k l) (patternGraphEdges_noOpposite k l)
    (patternCompressionKernel W b) (fun a p => patternCompressionKernel V b a (ρ a.1 p.1,ρ a.2 p.2))
    (fun a _ => patternCompressionKernel_measurable W b a) (fun a _ => hm a)
    (fun a _ => patternCompressionKernel_bounds W b a) (fun a _ => hb a)
    (fun _ => latinonAlignmentCost W V e f) (fun a _ => patternCompressionKernel_alignment_cut W V b e f a)
  rw [kernelGraphDensity_nodewise_relabel (patternGraphEdges k l) (patternGraphEdges_noOpposite k l)
    (patternCompressionKernel V b) (fun a _ => patternCompressionKernel_measurable V b a)
    (fun a _ => patternCompressionKernel_bounds V b a) ρ (patternVertexRelabel_preserving e f)] at h
  simpa only [Finset.sum_const,nsmul_eq_mul] using h

def patternPolynomialConstant {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) : ℕ :=
  k.factorial*l.factorial*(patternBinAssignments P q).card*(patternGraphEdges k l).card

theorem compressionPatternPolynomial_alignment {k l : ℕ} (W V : LatinonMeasure)
    (P : LatinOrderPattern k l) (q : ℕ) (e f : LatinonRelabel) :
    |compressionPatternPolynomial W P q-compressionPatternPolynomial V P q| ≤
      (patternPolynomialConstant P q : ℝ)*latinonAlignmentCost W V e f := by
  unfold compressionPatternPolynomial
  rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),← Finset.sum_sub_distrib]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*∑ b ∈ patternBinAssignments P q,
        |kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel W b)-
          kernelGraphDensity (patternGraphEdges k l) (patternCompressionKernel V b)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*∑ _b ∈ patternBinAssignments P q,
        ((patternGraphEdges k l).card : ℝ)*latinonAlignmentCost W V e f :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => patternCompressionGraph_alignment W V b e f))
        (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,patternPolynomialConstant,Nat.cast_mul]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.latinon_symbol_two_relabel_rectangle_integral
#print axioms LatinonEntropy.latinon_order_relabel_rectangle_integral
#print axioms LatinonEntropy.orderKernel_alignment_cut
#print axioms LatinonEntropy.symbolGridKernel_alignment_cut
#print axioms LatinonEntropy.patternVertexRelabel_preserving
#print axioms LatinonEntropy.patternCompressionKernel_alignment_cut
#print axioms LatinonEntropy.patternCompressionGraph_alignment
#print axioms LatinonEntropy.compressionPatternPolynomial_alignment
