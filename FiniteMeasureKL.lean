module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Fintype ι] [MeasurableSingletonClass ι] in
theorem finite_measure_ac_of_positive_reference (mu nu : Measure ι)
    (hnu : ∀ i, nu {i} ≠ 0) : mu ≪ nu := by
  intro S hS
  have he : S = ∅ := by
    apply Set.ext
    intro i
    constructor
    · intro hi
      exact hnu i (measure_mono_null (Set.singleton_subset_iff.mpr hi) hS)
    · intro hi
      exact False.elim hi
  rw [he,measure_empty]

/-- The derivative is determined pointwise, since every reference atom
has positive mass. No almost-everywhere representative is assumed. -/
theorem finite_rnDeriv_eq_ratio (mu nu : Measure ι) [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) (i : ι) : mu.rnDeriv nu i = mu {i}/nu {i} := by
  have hac := finite_measure_ac_of_positive_reference mu nu hnu
  have he := congrArg (fun m : Measure ι => m {i}) (Measure.withDensity_rnDeriv_eq mu nu hac)
  rw [withDensity_apply _ (measurableSet_singleton i),lintegral_singleton] at he
  apply (ENNReal.eq_div_iff (hnu i) (measure_ne_top nu {i})).mpr
  rwa [mul_comm]

theorem finite_measure_real_univ (mu : Measure ι) [IsFiniteMeasure mu] :
    (∑ i, mu.real {i}) = mu.real Set.univ := by
  have he := integral_fintype (μ := mu) (f := fun _ : ι => (1 : ℝ)) Integrable.of_finite
  simpa only [integral_const,smul_eq_mul,mul_one] using he.symm

theorem finite_kl_ne_top (mu nu : Measure ι) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) : InformationTheory.klDiv mu nu ≠ ⊤ :=
  InformationTheory.klDiv_ne_top (finite_measure_ac_of_positive_reference mu nu hnu) Integrable.of_finite

theorem finite_kl_toReal_eq_sum (mu nu : Measure ι) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) :
    (InformationTheory.klDiv mu nu).toReal =
      (∑ i, mu.real {i}*Real.log (mu.real {i}/nu.real {i}))+
        nu.real Set.univ-mu.real Set.univ := by
  have hac := finite_measure_ac_of_positive_reference mu nu hnu
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac,integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  simp_rw [finite_rnDeriv_eq_ratio mu nu hnu,ENNReal.toReal_div]
  have hterm : ∀ i, nu.real {i}*InformationTheory.klFun (mu.real {i}/nu.real {i}) =
      mu.real {i}*Real.log (mu.real {i}/nu.real {i})+nu.real {i}-mu.real {i} := by
    intro i
    have hv : nu.real {i} ≠ 0 := (ENNReal.toReal_pos (hnu i) (measure_ne_top nu {i})).ne'
    unfold InformationTheory.klFun
    calc
      _ = (nu.real {i}*(mu.real {i}/nu.real {i}))*Real.log (mu.real {i}/nu.real {i})+
        nu.real {i}-nu.real {i}*(mu.real {i}/nu.real {i}) := by ring
      _ = _ := by rw [mul_div_cancel₀ _ hv]
  change (∑ i, nu.real {i}*InformationTheory.klFun (mu.real {i}/nu.real {i})) = _
  simp_rw [hterm]
  rw [sum_sub_distrib,sum_add_distrib,finite_measure_real_univ nu,finite_measure_real_univ mu]

theorem finite_kl_eq_ofReal_sum (mu nu : Measure ι) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) :
    InformationTheory.klDiv mu nu = ENNReal.ofReal
      ((∑ i, mu.real {i}*Real.log (mu.real {i}/nu.real {i}))+
        nu.real Set.univ-mu.real Set.univ) := by
  rw [← finite_kl_toReal_eq_sum mu nu hnu,ENNReal.ofReal_toReal (finite_kl_ne_top mu nu hnu)]

theorem finite_probability_kl_eq_neg_table (mu nu : Measure ι)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (hnu : ∀ i, nu {i} ≠ 0) :
    InformationTheory.klDiv mu nu = ENNReal.ofReal
      (-(∑ i, mu.real {i}*Real.log (nu.real {i}/mu.real {i}))) := by
  rw [finite_kl_eq_ofReal_sum mu nu hnu,probReal_univ,probReal_univ,add_sub_cancel_right]
  apply congrArg ENNReal.ofReal
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hz : mu.real {i} = 0
  · simp only [hz,zero_mul,neg_zero]
  · have hv : nu.real {i} ≠ 0 := (ENNReal.toReal_pos (hnu i) (measure_ne_top nu {i})).ne'
    rw [Real.log_div hz hv,Real.log_div hv hz]
    ring

end LatinonEntropy

#print axioms LatinonEntropy.finite_measure_ac_of_positive_reference
#print axioms LatinonEntropy.finite_rnDeriv_eq_ratio
#print axioms LatinonEntropy.finite_measure_real_univ
#print axioms LatinonEntropy.finite_kl_ne_top
#print axioms LatinonEntropy.finite_kl_toReal_eq_sum
#print axioms LatinonEntropy.finite_kl_eq_ofReal_sum
#print axioms LatinonEntropy.finite_probability_kl_eq_neg_table
