module

public import LatinonCutInvariance
public import LatinonSymbolCompression

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def KernelCutClose (g h : I × I → ℝ) (eps : ℝ) : Prop :=
  ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
    |∫ p in S ×ˢ T, (g p-h p) ∂unitSquareVolume| ≤ eps

theorem kernelCutClose_of_L1 (g h : I × I → ℝ) (hg : Integrable g unitSquareVolume)
    (hh : Integrable h unitSquareVolume) (eps : ℝ)
    (herr : (∫ p, |g p-h p| ∂unitSquareVolume) ≤ eps) : KernelCutClose g h eps := by
  intro S T _ _
  exact (abs_integral_le_integral_abs.trans
    (setIntegral_le_integral (hg.sub hh).abs (ae_of_all _ (fun _ => abs_nonneg _)))).trans herr

theorem kernelCutClose_of_ae_abs_le (g h : I × I → ℝ) (hg : Integrable g unitSquareVolume)
    (hh : Integrable h unitSquareVolume) (eps : ℝ)
    (herr : ∀ᵐ p ∂unitSquareVolume, |g p-h p| ≤ eps) : KernelCutClose g h eps := by
  apply kernelCutClose_of_L1 g h hg hh eps
  calc
    (∫ p, |g p-h p| ∂unitSquareVolume) ≤ ∫ _p, eps ∂unitSquareVolume :=
      integral_mono_ae (hg.sub hh).abs (integrable_const _) herr
    _ = eps := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem kernelCutClose_triangle (g h z : I × I → ℝ)
    (hg : Integrable g unitSquareVolume) (hh : Integrable h unitSquareVolume)
    (hz : Integrable z unitSquareVolume) {a b : ℝ}
    (hgh : KernelCutClose g h a) (hhz : KernelCutClose h z b) : KernelCutClose g z (a+b) := by
  intro S T hS hT
  have he : (∫ p in S ×ˢ T, (g p-z p) ∂unitSquareVolume)=
      (∫ p in S ×ˢ T, (g p-h p) ∂unitSquareVolume)+
        (∫ p in S ×ˢ T, (h p-z p) ∂unitSquareVolume) := by
    rw [integral_sub hg.integrableOn hz.integrableOn,integral_sub hg.integrableOn hh.integrableOn,
      integral_sub hh.integrableOn hz.integrableOn]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hgh S T hS hT) (hhz S T hS hT))

theorem kernelCutClose_common_pullback (g h : I × I → ℝ) {eps : ℝ}
    (hclose : KernelCutClose g h eps) (e : LatinonRelabel) :
    KernelCutClose (fun p => g (e p.1,e p.2)) (fun p => h (e p.1,e p.2)) eps := by
  intro S T hS hT
  let ep : (I × I) ≃ᵐ (I × I) := e.equiv.prodCongr e.equiv
  have hm : MeasurePreserving ep unitSquareVolume unitSquareVolume := e.preserves.prod e.preserves
  have hset : ep ⁻¹' ((e.symm ⁻¹' S) ×ˢ (e.symm ⁻¹' T))=S ×ˢ T := by
    ext p
    change (e.symm (e p.1) ∈ S ∧ e.symm (e p.2) ∈ T) ↔ (p.1 ∈ S ∧ p.2 ∈ T)
    rw [e.symm_apply_apply,e.symm_apply_apply]
  have hchange := hm.setIntegral_preimage_emb ep.measurableEmbedding (fun p => g p-h p)
    ((e.symm ⁻¹' S) ×ˢ (e.symm ⁻¹' T))
  rw [hset] at hchange
  change |∫ p in S ×ˢ T, (fun q => g q-h q) (ep p) ∂unitSquareVolume| ≤ eps
  rw [hchange]
  exact hclose _ _ (hS.preimage e.symm.measurable) (hT.preimage e.symm.measurable)

/-- Changing two bounded kernels only on row/column exceptional strips
costs at most twice the one-dimensional exceptional mass. -/
theorem kernel_L1_le_two_bad_strips (g h : I × I → ℝ)
    (hg : Integrable g unitSquareVolume) (hh : Integrable h unitSquareVolume)
    (hgb : ∀ᵐ p ∂unitSquareVolume, g p ∈ Set.Icc (0 : ℝ) 1)
    (hhb : ∀ᵐ p ∂unitSquareVolume, h p ∈ Set.Icc (0 : ℝ) 1)
    (bad : Set I) (hbad : MeasurableSet bad)
    (heq : ∀ᵐ p ∂unitSquareVolume, p.1 ∉ bad → p.2 ∉ bad → g p=h p) :
    (∫ p, |g p-h p| ∂unitSquareVolume) ≤ 2*(volume : Measure I).real bad := by
  let strip : Set (I × I) := (bad ×ˢ Set.univ) ∪ (Set.univ ×ˢ bad)
  have hstrip : MeasurableSet strip :=
    (hbad.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hbad)
  have hdom : ∀ᵐ p ∂unitSquareVolume, |g p-h p| ≤ strip.indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [hgb,hhb,heq] with p hp hq he
    by_cases hs : p ∈ strip
    · rw [Set.indicator_of_mem hs]
      exact abs_sub_le_one_of_unit_bounds hp hq
    · rw [Set.indicator_of_notMem hs]
      have h1 : p.1 ∉ bad := fun hb => hs (Or.inl ⟨hb,Set.mem_univ _⟩)
      have h2 : p.2 ∉ bad := fun hb => hs (Or.inr ⟨Set.mem_univ _,hb⟩)
      rw [he h1 h2,sub_self,abs_zero]
  calc
    (∫ p, |g p-h p| ∂unitSquareVolume) ≤
        ∫ p, strip.indicator (fun _ => (1 : ℝ)) p ∂unitSquareVolume :=
      integral_mono_ae (hg.sub hh).abs ((integrable_const _).indicator hstrip) hdom
    _ = unitSquareVolume.real strip := integral_indicator_one hstrip
    _ ≤ unitSquareVolume.real (bad ×ˢ Set.univ)+unitSquareVolume.real (Set.univ ×ˢ bad) :=
      measureReal_union_le _ _
    _ = 2*(volume : Measure I).real bad := by
      rw [measureReal_prod_prod,measureReal_prod_prod,probReal_univ,mul_one,one_mul]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.kernelCutClose_of_L1
#print axioms LatinonEntropy.kernelCutClose_of_ae_abs_le
#print axioms LatinonEntropy.kernelCutClose_triangle
#print axioms LatinonEntropy.kernelCutClose_common_pullback
#print axioms LatinonEntropy.kernel_L1_le_two_bad_strips
