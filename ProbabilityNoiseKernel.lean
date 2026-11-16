module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

/-- Retain the input with weight a,or resample from the reference with weight b. -/
def probabilityNoiseKernel {α : Type*} [MeasurableSpace α]
    (nu : Measure α) (a b : ℝ≥0∞) : Kernel α α where
  toFun x := a • Measure.dirac x + b • nu
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    have hd : Measurable (fun x : α => Measure.dirac x E) := by
      simpa only [Kernel.id_apply] using (Kernel.id : Kernel α α).measurable_coe hE
    exact (measurable_const.mul hd).add measurable_const

theorem probabilityNoiseKernel_markov {α : Type*} [MeasurableSpace α]
    (nu : Measure α) [IsProbabilityMeasure nu] (a b : ℝ≥0∞) (hab : a+b=1) :
    IsMarkovKernel (probabilityNoiseKernel nu a b) := by
  constructor
  intro x
  constructor
  simpa only [probabilityNoiseKernel,Kernel.coe_mk,Measure.add_apply,
    Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem (Set.mem_univ x),
    measure_univ,mul_one] using hab

theorem probabilityNoiseKernel_comp {α : Type*} [MeasurableSpace α]
    (mu nu : Measure α) [IsProbabilityMeasure mu] (a b : ℝ≥0∞) :
    probabilityNoiseKernel nu a b ∘ₘ mu = a • mu+b • nu := by
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE (probabilityNoiseKernel nu a b).aemeasurable]
  change (∫⁻ x, (a • Measure.dirac x+b • nu) E ∂mu) = _
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  have hd : Measurable (fun x : α => Measure.dirac x E) :=
    by simpa only [Kernel.id_apply] using (Kernel.id : Kernel α α).measurable_coe hE
  have had : Measurable (fun x : α => a*Measure.dirac x E) := measurable_const.mul hd
  rw [lintegral_add_left had,lintegral_const_mul a hd,lintegral_const]
  have hid : (∫⁻ x, Measure.dirac x E ∂mu) = mu E := by
    simpa only [Measure.id_comp,Kernel.id_apply] using
      (Measure.bind_apply hE (Kernel.id : Kernel α α).aemeasurable).symm
  rw [hid,measure_univ,mul_one]

/-- Mixing any probability with its reference cannot increase relative entropy. -/
theorem klDiv_probability_noise_le {α : Type*} [MeasurableSpace α]
    (mu nu : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (a b : ℝ≥0∞) (hab : a+b=1) :
    klDiv (a • mu+b • nu) nu ≤ klDiv mu nu := by
  have := probabilityNoiseKernel_markov nu a b hab
  have hh := klDiv_comp_right_le mu nu (probabilityNoiseKernel nu a b)
  rw [probabilityNoiseKernel_comp mu nu a b,probabilityNoiseKernel_comp nu nu a b,
    ← add_smul,hab,one_smul] at hh
  exact hh

end LatinonEntropy

#print axioms LatinonEntropy.probabilityNoiseKernel
#print axioms LatinonEntropy.probabilityNoiseKernel_markov
#print axioms LatinonEntropy.probabilityNoiseKernel_comp
#print axioms LatinonEntropy.klDiv_probability_noise_le
