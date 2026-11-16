module

public import LatinonSymbolKernelCompression

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonSymbolKernel_real_mem_Icc (W : LatinonMeasure) (U : Set I) (p : I × I) :
    (latinonSymbolKernel W p).real U ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  exact measureReal_le_one

/-- Each conditional symbol event has the prescribed uniform mean in
almost every row. This uses the xz marginal, including for singular W. -/
theorem latinonSymbolKernel_row_mean (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    (fun x => ∫ y, (latinonSymbolKernel W (x,y)).real U ∂volume)=ᵐ[volume]
      (fun _ : I => (volume : Measure I).real U) := by
  have hi := integrable_real_latinonSymbolKernel_event W U hU
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi.integral_prod_left (integrable_const _)
  intro S hS _
  have he := setIntegral_prod (fun p => (latinonSymbolKernel W p).real U)
    (s := S) (t := Set.univ) hi.integrableOn
  simp only [Measure.restrict_univ] at he
  rw [← he,latinonSymbolKernel_real_rectangle W S Set.univ U hS MeasurableSet.univ hU,
    W.xz_uniform_real S U hS hU,setIntegral_const,smul_eq_mul]

/-- The corresponding column identity follows from the yz marginal. -/
theorem latinonSymbolKernel_col_mean (W : LatinonMeasure) (U : Set I)
    (hU : MeasurableSet U) :
    (fun y => ∫ x, (latinonSymbolKernel W (x,y)).real U ∂volume)=ᵐ[volume]
      (fun _ : I => (volume : Measure I).real U) := by
  have hi := integrable_real_latinonSymbolKernel_event W U hU
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi.integral_prod_right (integrable_const _)
  intro T hT _
  have he := setIntegral_prod (fun p : I × I => (latinonSymbolKernel W p.swap).real U)
    (s := T) (t := Set.univ) hi.swap.integrableOn
  simp only [Measure.restrict_univ,Prod.swap_prod_mk] at he
  rw [← he,setIntegral_prod_swap Set.univ T (fun p => (latinonSymbolKernel W p).real U),
    latinonSymbolKernel_real_rectangle W Set.univ T U MeasurableSet.univ hT hU,
    W.yz_uniform_real T U hT hU,setIntegral_const,smul_eq_mul]

theorem latinonSymbolKernel_mean (W : LatinonMeasure) (U : Set I) (hU : MeasurableSet U) :
    (∫ p, (latinonSymbolKernel W p).real U ∂unitSquareVolume)=(volume : Measure I).real U := by
  rw [integral_prod _ (integrable_real_latinonSymbolKernel_event W U hU),
    integral_congr_ae (latinonSymbolKernel_row_mean W U hU)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

end LatinonEntropy

#print axioms LatinonEntropy.latinonSymbolKernel_real_mem_Icc
#print axioms LatinonEntropy.latinonSymbolKernel_row_mean
#print axioms LatinonEntropy.latinonSymbolKernel_col_mean
#print axioms LatinonEntropy.latinonSymbolKernel_mean
