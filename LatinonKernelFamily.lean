module

public import LatinonSymbolGridControl
public import LatinonSynchronousCompleteness
public import KernelCutEstimates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def latinonOrderKernel (W : LatinonMeasure) : I × I → ℝ :=
  (orderRelation W.order).indicator (fun _ => (1 : ℝ))

theorem latinonOrderKernel_measurable (W : LatinonMeasure) : Measurable (latinonOrderKernel W) :=
  measurable_const.indicator (orderRelation_measurable W.order W.order_preserving.measurable)

theorem latinonOrderKernel_bounds (W : LatinonMeasure) (p : I × I) :
    latinonOrderKernel W p ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : p ∈ orderRelation W.order <;> simp [latinonOrderKernel,h]

theorem latinonOrderKernel_integrable (W : LatinonMeasure) : Integrable (latinonOrderKernel W) unitSquareVolume :=
  Integrable.of_mem_Icc 0 1 (latinonOrderKernel_measurable W).aemeasurable
    (ae_of_all _ (latinonOrderKernel_bounds W))

theorem orderBox_eq_orderKernel_integral (W : LatinonMeasure) (R : LatinonRectangle) :
    orderBox W.order R=∫ p in R.rows ×ˢ R.cols, latinonOrderKernel W p ∂unitSquareVolume := by
  unfold latinonOrderKernel
  rw [setIntegral_indicator (orderRelation_measurable W.order W.order_preserving.measurable),
    setIntegral_const,smul_eq_mul,mul_one]
  rfl

theorem orderCut_le_of_orderKernel_close (W V : LatinonMeasure) {eps : ℝ}
    (h : KernelCutClose (latinonOrderKernel W) (latinonOrderKernel V) eps) :
    orderCut W.order V.order ≤ eps := by
  apply cutValueSup_le
  intro R
  rw [orderBox_eq_orderKernel_integral W R,orderBox_eq_orderKernel_integral V R,
    ← integral_sub (latinonOrderKernel_integrable W).integrableOn (latinonOrderKernel_integrable V).integrableOn]
  exact h R.rows R.cols R.rows_measurable R.cols_measurable

def latinonKernelFamily (W : LatinonMeasure) (n : ℕ) : Fin (n+1) → I × I → ℝ :=
  Fin.cases (latinonOrderKernel W) (fun j => latinonSymbolCompression W (lebesgueGridCell j))

theorem latinonKernelFamily_measurable (W : LatinonMeasure) (n : ℕ) (j : Fin (n+1)) :
    Measurable (latinonKernelFamily W n j) := by
  refine Fin.cases (latinonOrderKernel_measurable W) (fun i => ?_) j
  exact latinonSymbolCompression_measurable W _

theorem latinonKernelFamily_bounds (W : LatinonMeasure) (n : ℕ) (j : Fin (n+1)) :
    ∀ᵐ p ∂unitSquareVolume, latinonKernelFamily W n j p ∈ Set.Icc (0 : ℝ) 1 := by
  refine Fin.cases (ae_of_all _ (latinonOrderKernel_bounds W)) (fun i => ?_) j
  exact latinonSymbolCompression_bounds W _

theorem latinonKernelFamily_integrable (W : LatinonMeasure) (n : ℕ) (j : Fin (n+1)) :
    Integrable (latinonKernelFamily W n j) unitSquareVolume :=
  Integrable.of_mem_Icc 0 1 (latinonKernelFamily_measurable W n j).aemeasurable
    (latinonKernelFamily_bounds W n j)

theorem latinon_symbol_relabel_rectangle_integral (W : LatinonMeasure) (e : LatinonRelabel)
    (U S T : Set I) (hU : MeasurableSet U) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (synchronousRelabel W e).measure.real ((S ×ˢ T) ×ˢ U)=
      ∫ p in S ×ˢ T, latinonSymbolCompression W U (e p.1,e p.2) ∂unitSquareVolume := by
  let ep : (I × I) ≃ᵐ (I × I) := e.equiv.prodCongr e.equiv
  have hm : MeasurePreserving ep unitSquareVolume unitSquareVolume := e.preserves.prod e.preserves
  have hset : ep ⁻¹' ((e.symm ⁻¹' S) ×ˢ (e.symm ⁻¹' T))=S ×ˢ T := by
    ext p
    change (e.symm (e p.1) ∈ S ∧ e.symm (e p.2) ∈ T) ↔ (p.1 ∈ S ∧ p.2 ∈ T)
    rw [e.symm_apply_apply,e.symm_apply_apply]
  have he := hm.setIntegral_preimage_emb ep.measurableEmbedding (latinonSymbolCompression W U)
    ((e.symm ⁻¹' S) ×ˢ (e.symm ⁻¹' T))
  rw [hset] at he
  change (relabelLatinonMeasure W.measure e e).real ((S ×ˢ T) ×ˢ U)=_
  rw [relabelLatinonMeasure_real_box _ e e S T U hS hT hU,
    ← latinonSymbolCompression_rectangle W U _ _ (hS.preimage e.symm.measurable) (hT.preimage e.symm.measurable)]
  exact he.symm

theorem kernelCutClose_symm (g h : I × I → ℝ) {eps : ℝ}
    (hc : KernelCutClose g h eps) : KernelCutClose h g eps := by
  intro S T hS hT
  have he : (fun p => h p-g p)=(fun p => -(g p-h p)) := by funext p; ring
  rw [he,integral_neg,abs_neg]
  exact hc S T hS hT

/-- Agreement with the SAME finite prototype controls BOTH order terms
and the full distribution norm,without density assumptions on W or V. -/
theorem rawCutCost_le_of_common_family_approximation (W V : LatinonMeasure)
    {n : ℕ} (hn : 0 < n) (e f : LatinonRelabel) (v : Fin (n+1) → I × I → ℝ)
    (hv : ∀ j, Measurable (v j) ∧ (∀ p, v j p ∈ Set.Icc (0 : ℝ) 1))
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hW : ∀ j, KernelCutClose (fun p => latinonKernelFamily W n j (e p.1,e p.2)) (v j) delta)
    (hV : ∀ j, KernelCutClose (fun p => latinonKernelFamily V n j (f p.1,f p.2)) (v j) delta) :
    latinonRawCutCost (synchronousRelabel W e) (synchronousRelabel V f) ≤
      ((n : ℝ)+2)*(2*delta)+4/(n : ℝ) := by
  have hpair (j : Fin (n+1)) :
      KernelCutClose (fun p => latinonKernelFamily W n j (e p.1,e p.2))
        (fun p => latinonKernelFamily V n j (f p.1,f p.2)) (2*delta) := by
    have hwi : Integrable (fun p : I × I => latinonKernelFamily W n j (e p.1,e p.2)) unitSquareVolume :=
      (e.preserves.prod e.preserves).integrable_comp_of_integrable (latinonKernelFamily_integrable W n j)
    have hvi : Integrable (fun p : I × I => latinonKernelFamily V n j (f p.1,f p.2)) unitSquareVolume :=
      (f.preserves.prod f.preserves).integrable_comp_of_integrable (latinonKernelFamily_integrable V n j)
    have hpi : Integrable (v j) unitSquareVolume := Integrable.of_mem_Icc 0 1
      (hv j).1.aemeasurable (ae_of_all _ (hv j).2)
    simpa only [two_mul] using kernelCutClose_triangle _ _ _ hwi hpi hvi (hW j)
      (kernelCutClose_symm _ _ (hV j))
  have hzero : KernelCutClose (latinonOrderKernel (synchronousRelabel W e))
      (latinonOrderKernel (synchronousRelabel V f)) (2*delta) := hpair 0
  have horder := orderCut_le_of_orderKernel_close _ _ hzero
  have hcell (j : Fin n) (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
      |(synchronousRelabel W e).measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)-
        (synchronousRelabel V f).measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)| ≤ 2*delta := by
    have hwi : Integrable (fun p : I × I => latinonSymbolCompression W (lebesgueGridCell j) (e p.1,e p.2))
        unitSquareVolume := (e.preserves.prod e.preserves).integrable_comp_of_integrable
      (latinonSymbolCompression_integrable W _)
    have hvi : Integrable (fun p : I × I => latinonSymbolCompression V (lebesgueGridCell j) (f p.1,f p.2))
        unitSquareVolume := (f.preserves.prod f.preserves).integrable_comp_of_integrable
      (latinonSymbolCompression_integrable V _)
    rw [latinon_symbol_relabel_rectangle_integral W e _ S T (lebesgueGridCell_measurable j) hS hT,
      latinon_symbol_relabel_rectangle_integral V f _ S T (lebesgueGridCell_measurable j) hS hT,
      ← integral_sub hwi.integrableOn hvi.integrableOn]
    exact hpair j.succ S T hS hT
  have hmeasure := measureCut_le_symbol_grid_tests (synchronousRelabel W e) (synchronousRelabel V f)
    hn (2*delta) (mul_nonneg (by norm_num) hdelta) hcell
  unfold latinonRawCutCost
  calc
    _ ≤ 2*(2*delta)+((n : ℝ)*(2*delta)+4/(n : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left horder (by norm_num)) hmeasure
    _ = _ := by ring

theorem synchronousCutDistance_le_aligned_rawCost (W V : LatinonMeasure) (e f : LatinonRelabel) :
    synchronousCutDistance W V ≤ latinonRawCutCost (synchronousRelabel W e) (synchronousRelabel V f) := by
  have hz : synchronousCutDistance W (synchronousRelabel W e)=0 := by
    rw [synchronousCutDistance_symm]
    exact synchronousCutDistance_relabel_zero W e
  calc
    synchronousCutDistance W V ≤ synchronousCutDistance W (synchronousRelabel W e)+
        synchronousCutDistance (synchronousRelabel W e) V := synchronousCutDistance_triangle _ _ _
    _ ≤ synchronousCutDistance W (synchronousRelabel W e)+
        (synchronousCutDistance (synchronousRelabel W e) (synchronousRelabel V f)+
          synchronousCutDistance (synchronousRelabel V f) V) :=
      add_le_add le_rfl (synchronousCutDistance_triangle _ _ _)
    _ = synchronousCutDistance (synchronousRelabel W e) (synchronousRelabel V f) := by
      rw [hz,synchronousCutDistance_relabel_zero,zero_add,add_zero]
    _ ≤ _ := synchronousCutDistance_le_rawCost _ _

end LatinonEntropy

#print axioms LatinonEntropy.latinonOrderKernel_measurable
#print axioms LatinonEntropy.latinonOrderKernel_bounds
#print axioms LatinonEntropy.latinonOrderKernel_integrable
#print axioms LatinonEntropy.orderBox_eq_orderKernel_integral
#print axioms LatinonEntropy.orderCut_le_of_orderKernel_close
#print axioms LatinonEntropy.latinonKernelFamily_measurable
#print axioms LatinonEntropy.latinonKernelFamily_bounds
#print axioms LatinonEntropy.latinonKernelFamily_integrable
#print axioms LatinonEntropy.latinon_symbol_relabel_rectangle_integral
#print axioms LatinonEntropy.kernelCutClose_symm
#print axioms LatinonEntropy.rawCutCost_le_of_common_family_approximation
#print axioms LatinonEntropy.synchronousCutDistance_le_aligned_rawCost
