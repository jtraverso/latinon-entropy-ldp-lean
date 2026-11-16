module

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory

theorem abs_mass_sub_density_integral_le {α : Type*} [MeasurableSpace α]
    (mu rho : Measure α) [IsFiniteMeasure mu] [IsFiniteMeasure rho]
    (hac : mu ≪ rho) (q : α → ℝ) (hq : Integrable q rho) (E : Set α) :
    |mu.real E-(∫ x in E, q x ∂rho)| ≤
      ∫ x, |(mu.rnDeriv rho x).toReal-q x| ∂rho := by
  have hRN : Integrable (fun x => (mu.rnDeriv rho x).toReal) rho := Measure.integrable_toReal_rnDeriv
  have hdiff : Integrable (fun x => (mu.rnDeriv rho x).toReal-q x) rho := hRN.sub hq
  rw [← Measure.setIntegral_toReal_rnDeriv hac E,← integral_sub hRN.integrableOn hq.integrableOn]
  calc
    |∫ x in E, (mu.rnDeriv rho x).toReal-q x ∂rho|
        ≤ ∫ x in E, |(mu.rnDeriv rho x).toReal-q x| ∂rho := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x => (mu.rnDeriv rho x).toReal-q x) (μ := rho.restrict E)
    _ ≤ ∫ x, |(mu.rnDeriv rho x).toReal-q x| ∂rho :=
      setIntegral_le_integral hdiff.abs (ae_of_all _ fun _ => abs_nonneg _)

end LatinonEntropy

#print axioms LatinonEntropy.abs_mass_sub_density_integral_le
