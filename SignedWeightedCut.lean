module

public import SignedWeightedIntegral
public import KernelCutEstimates

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Rectangle control for a signed integrable kernel implies the weighted
cut bound with constant one. Both weights need only lie in [0,1] a.e. -/
theorem abs_integral_separable_weight_le_of_rectangle_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
    (K : X × Y → ℝ) (hKm : Measurable K) (hK : Integrable K (mu.prod nu))
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ᵐ x ∂mu, f x ∈ Set.Icc (0 : ℝ) 1)
    (hgb : ∀ᵐ y ∂nu, g y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (hcut : ∀ (S : Set X) (T : Set Y), MeasurableSet S → MeasurableSet T →
      |∫ p in S ×ˢ T, K p ∂mu.prod nu| ≤ eps) :
    |∫ p, (f p.1*g p.2)*K p ∂mu.prod nu| ≤ eps := by
  let L : X × Y → ℝ := fun p => f p.1*K p
  have hLm : Measurable L := (hf.comp measurable_fst).mul hKm
  have hLi : Integrable L (mu.prod nu) := integrable_unit_weight (mu.prod nu) K
    (fun p => f p.1) hK (hf.comp measurable_fst) (Measure.quasiMeasurePreserving_fst.ae hfb)
  let q : Y → ℝ := fun y => ∫ x, L (x,y) ∂mu
  have hqm : Measurable q := hLm.stronglyMeasurable.integral_prod_left'.measurable
  have hqi : Integrable q nu := hLi.integral_prod_right
  have hqset (T : Set Y) (hT : MeasurableSet T) : |∫ y in T, q y ∂nu| ≤ eps := by
    have hKr : Integrable K (mu.prod (nu.restrict T)) :=
      hK.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hLr : Integrable L (mu.prod (nu.restrict T)) :=
      hLi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    let kT : X → ℝ := fun x => ∫ y in T, K (x,y) ∂nu
    have hkTm : Measurable kT := hKm.stronglyMeasurable.integral_prod_right'.measurable
    have hkTi : Integrable kT mu := hKr.integral_prod_left
    have hkTset (S : Set X) (hS : MeasurableSet S) : |∫ x in S, kT x ∂mu| ≤ eps := by
      change |∫ x in S, ∫ y in T, K (x,y) ∂nu ∂mu| ≤ eps
      rw [← setIntegral_prod K hK.integrableOn]
      exact hcut S T hS hT
    have hw := abs_integral_unit_weight_le_of_set_bound mu kT f hkTm hkTi hf hfb eps hkTset
    calc
      |∫ y in T, q y ∂nu| = |∫ p, L p ∂mu.prod (nu.restrict T)| :=
        congrArg abs (integral_prod_symm L hLr).symm
      _ = |∫ x, f x*kT x ∂mu| := by
        rw [integral_prod L hLr]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (fun x => integral_const_mul (f x) (fun y => K (x,y)))
      _ ≤ eps := hw
  have hw := abs_integral_unit_weight_le_of_set_bound nu q g hqm hqi hg hgb eps hqset
  have hWi : Integrable (fun p : X × Y => g p.2*L p) (mu.prod nu) :=
    integrable_unit_weight (mu.prod nu) L (fun p => g p.2) hLi
      (hg.comp measurable_snd) (Measure.quasiMeasurePreserving_snd.ae hgb)
  calc
    |∫ p, (f p.1*g p.2)*K p ∂mu.prod nu| = |∫ p, g p.2*L p ∂mu.prod nu| := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by dsimp [L]; ring)
    _ = |∫ y, g y*q y ∂nu| := by
      rw [integral_prod_symm _ hWi]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun y => integral_const_mul (g y) (fun x => L (x,y)))
    _ ≤ eps := hw

theorem kernelCutClose_weighted (K H : I × I → ℝ)
    (hKm : Measurable K) (hHm : Measurable H)
    (hK : Integrable K unitSquareVolume) (hH : Integrable H unitSquareVolume)
    (f g : I → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ᵐ x ∂(volume : Measure I), f x ∈ Set.Icc (0 : ℝ) 1)
    (hgb : ∀ᵐ y ∂(volume : Measure I), g y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (hcut : KernelCutClose K H eps) :
    |∫ p, (f p.1*g p.2)*(K p-H p) ∂unitSquareVolume| ≤ eps :=
  abs_integral_separable_weight_le_of_rectangle_bound volume volume (fun p => K p-H p)
    (hKm.sub hHm) (hK.sub hH) f g hf hg hfb hgb eps hcut

end LatinonEntropy

#print axioms LatinonEntropy.abs_integral_separable_weight_le_of_rectangle_bound
#print axioms LatinonEntropy.kernelCutClose_weighted
