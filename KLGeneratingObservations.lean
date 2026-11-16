module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.Probability.Martingale.Convergence

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal ProbabilityTheory

variable {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
  (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The extended-valued formula needs no integrability of the log likelihood. -/
theorem klDiv_map_eq_condExp_lintegral (hac : μ ≪ ν) {g : α → γ} (hg : Measurable g) :
    klDiv (μ.map g) (ν.map g) =
      ∫⁻ x, ENNReal.ofReal (klFun ((ν[fun x => (μ.rnDeriv ν x).toReal |
        (inferInstance : MeasurableSpace γ).comap g]) x)) ∂ν := by
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hg)]
  rw [lintegral_map (by fun_prop) hg]
  apply lintegral_congr_ae
  filter_upwards [toReal_rnDeriv_map hac hg] with x hx
  rw [hx]

/-- Increasing observations that generate the ambient sigma-algebra recover
all KL divergence for absolutely continuous finite measures, including infinity. -/
theorem klDiv_eq_iSup_generating_maps_of_ac
    {β : ℕ → Type*} [∀ k, MeasurableSpace (β k)]
    (hac : μ ≪ ν) (g : ∀ k, α → β k) (hg : ∀ k, Measurable (g k))
    (hmono : Monotone (fun k => (inferInstance : MeasurableSpace (β k)).comap (g k)))
    (hgen : (⨆ k, (inferInstance : MeasurableSpace (β k)).comap (g k)) =
      (inferInstance : MeasurableSpace α)) :
    klDiv μ ν = ⨆ k, klDiv (μ.map (g k)) (ν.map (g k)) := by
  let F : Filtration ℕ (inferInstance : MeasurableSpace α) :=
    ⟨(fun k => (inferInstance : MeasurableSpace (β k)).comap (g k)),hmono,
      fun k => (hg k).comap_le⟩
  let f : α → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hf : Integrable f ν := Measure.integrable_toReal_rnDeriv
  have hfm : StronglyMeasurable[⨆ k, F k] f := by
    change StronglyMeasurable[⨆ k, (inferInstance : MeasurableSpace (β k)).comap (g k)] f
    rw [hgen]
    exact (Measure.measurable_rnDeriv μ ν).ennreal_toReal.stronglyMeasurable
  have hc := hf.tendsto_ae_condExp (ℱ := F) hfm
  let u : ℕ → α → ℝ≥0∞ := fun k x => ENNReal.ofReal (klFun ((ν[f | F k]) x))
  have hu : ∀ k, Measurable (u k) := by
    intro k
    exact ENNReal.continuous_ofReal.measurable.comp (measurable_klFun.comp
      ((stronglyMeasurable_condExp.mono (F.le k)).measurable))
  have hl : (fun x => liminf (fun k => u k x) atTop) =ᵐ[ν]
      (fun x => ENNReal.ofReal (klFun (f x))) := by
    filter_upwards [hc] with x hx
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (continuous_klFun.continuousAt.tendsto.comp hx)).liminf_eq
  apply le_antisymm
  · rw [klDiv_eq_lintegral_klFun_of_ac hac]
    calc
      (∫⁻ x, ENNReal.ofReal (klFun ((μ.rnDeriv ν x).toReal)) ∂ν)
          = ∫⁻ x, liminf (fun k => u k x) atTop ∂ν := (lintegral_congr_ae hl).symm
      _ ≤ liminf (fun k => ∫⁻ x, u k x ∂ν) atTop := lintegral_liminf_le hu
      _ ≤ ⨆ k, ∫⁻ x, u k x ∂ν := le_trans (liminf_le_limsup) limsup_le_iSup
      _ = ⨆ k, klDiv (μ.map (g k)) (ν.map (g k)) := by
        congr 1
        funext k
        exact (klDiv_map_eq_condExp_lintegral μ ν hac (hg k)).symm
  · exact iSup_le fun k => klDiv_map_le μ ν (hg k)

end LatinonEntropy

#print axioms LatinonEntropy.klDiv_map_eq_condExp_lintegral
#print axioms LatinonEntropy.klDiv_eq_iSup_generating_maps_of_ac
