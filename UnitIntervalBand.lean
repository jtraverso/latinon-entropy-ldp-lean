module

public import LebesgueGridPartition
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def unitBand (r : ℝ) : Set (I × I) := {p | |(p.1 : ℝ)-(p.2 : ℝ)| ≤ r}

theorem unitBand_measurable (r : ℝ) : MeasurableSet (unitBand r) := by
  have hm : Measurable (fun p : I × I => (p.1 : ℝ)-(p.2 : ℝ)) :=
    (measurable_subtype_coe.comp measurable_fst).sub (measurable_subtype_coe.comp measurable_snd)
  simpa only [unitBand,Real.norm_eq_abs] using measurableSet_le hm.norm (measurable_const (a := r))

def unitBandFiber (r : ℝ) (u : I) : Set I := {v | |(u : ℝ)-(v : ℝ)| ≤ r}

theorem unitBandFiber_measurable (r : ℝ) (u : I) : MeasurableSet (unitBandFiber r u) := by
  have hm : Measurable (fun v : I => (u : ℝ)-(v : ℝ)) := measurable_const.sub measurable_subtype_coe
  simpa only [unitBandFiber,Real.norm_eq_abs] using measurableSet_le hm.norm (measurable_const (a := r))

theorem unitBandFiber_mass (r : ℝ) (hr : 0 ≤ r) (u : I) :
    (volume : Measure I).real (unitBandFiber r u) ≤ 2*r := by
  have hsubset : ((↑) : I → ℝ) '' unitBandFiber r u ⊆ Set.Icc ((u : ℝ)-r) ((u : ℝ)+r) := by
    rintro _ ⟨v,hv,rfl⟩
    change |(u : ℝ)-(v : ℝ)| ≤ r at hv
    have hb := abs_le.mp hv
    exact ⟨by linarith only [hb.2],by linarith only [hb.1]⟩
  rw [measureReal_def,unitInterval.volume_apply]
  calc
    ((volume : Measure ℝ) (((↑) : I → ℝ) '' unitBandFiber r u)).toReal
        ≤ ((volume : Measure ℝ) (Set.Icc ((u : ℝ)-r) ((u : ℝ)+r))).toReal :=
          ENNReal.toReal_mono (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hsubset)
    _ = 2*r := by
      rw [Real.volume_Icc,ENNReal.toReal_ofReal (by linarith only [hr])]
      ring

theorem unitBand_mass (r : ℝ) (hr : 0 ≤ r) :
    ((volume : Measure I).prod volume).real (unitBand r) ≤ 2*r := by
  let F := (unitBand r).indicator (fun _ : I × I => (1 : ℝ))
  have hF : Integrable F ((volume : Measure I).prod volume) :=
    (integrable_const 1).indicator (unitBand_measurable r)
  have hmass : ((volume : Measure I).prod volume).real (unitBand r) =
      ∫ p, F p ∂((volume : Measure I).prod volume) := by
    rw [integral_indicator (unitBand_measurable r),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
  have hfiber : ∀ u : I, (∫ v : I, F (u,v)) = (volume : Measure I).real (unitBandFiber r u) := by
    intro u
    have he : (fun v : I => F (u,v)) = (unitBandFiber r u).indicator (fun _ => (1 : ℝ)) := rfl
    rw [he,integral_indicator (unitBandFiber_measurable r u),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
  rw [hmass,integral_prod F hF]
  simp_rw [hfiber]
  calc
    (∫ u : I, (volume : Measure I).real (unitBandFiber r u)) ≤ ∫ _ : I, 2*r := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => measureReal_nonneg) (integrable_const _)
      exact ae_of_all _ (unitBandFiber_mass r hr)
    _ = 2*r := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem mp_unitBand_mass (f : I → I) (hf : MeasurePreserving f volume volume) (r : ℝ) (hr : 0 ≤ r) :
    ((volume : Measure I).prod volume).real
      {p : I × I | |(f p.1 : ℝ)-(f p.2 : ℝ)| ≤ r} ≤ 2*r := by
  have hm := (hf.prod hf).measureReal_preimage (unitBand_measurable r).nullMeasurableSet
  change ((volume : Measure I).prod volume).real
      {p : I × I | |(f p.1 : ℝ)-(f p.2 : ℝ)| ≤ r} =
    ((volume : Measure I).prod volume).real (unitBand r) at hm
  rw [hm]
  exact unitBand_mass r hr

end LatinonEntropy

#print axioms LatinonEntropy.unitBand_measurable
#print axioms LatinonEntropy.unitBandFiber_measurable
#print axioms LatinonEntropy.unitBandFiber_mass
#print axioms LatinonEntropy.unitBand_mass
#print axioms LatinonEntropy.mp_unitBand_mass
