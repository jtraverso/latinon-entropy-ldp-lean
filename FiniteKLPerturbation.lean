module

public import FiniteMeasureKL
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Finset
open scoped Classical ENNReal NNReal

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem finite_atom_cost_nonneg (m v : ℝ) (hm : 0 ≤ m) (hv : 0 < v) :
    0 ≤ m*Real.log (m/v)+v-m := by
  have he : v*klFun (m/v) = m*Real.log (m/v)+v-m := by
    unfold klFun
    rw [mul_sub,mul_add,← mul_assoc,mul_div_cancel₀ _ hv.ne',mul_one]
  rw [← he]
  exact mul_nonneg hv.le (klFun_nonneg (div_nonneg hm hv.le))

theorem finite_kl_eq_sum_atom_cost (mu nu : Measure ι) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) :
    klDiv mu nu = ENNReal.ofReal (∑ i,
      (mu.real {i}*Real.log (mu.real {i}/nu.real {i})+nu.real {i}-mu.real {i})) := by
  rw [finite_kl_eq_ofReal_sum mu nu hnu,sum_sub_distrib,sum_add_distrib,
    finite_measure_real_univ nu,finite_measure_real_univ mu]

theorem finite_atom_cost_le_kl (mu nu : Measure ι) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) (i : ι) :
    ENNReal.ofReal (mu.real {i}*Real.log (mu.real {i}/nu.real {i})+nu.real {i}-mu.real {i}) ≤
      klDiv mu nu := by
  rw [finite_kl_eq_sum_atom_cost mu nu hnu]
  apply ENNReal.ofReal_le_ofReal
  apply single_le_sum _ (mem_univ i)
  intro j _
  exact finite_atom_cost_nonneg _ _ measureReal_nonneg
    (ENNReal.toReal_pos (hnu j) (measure_ne_top nu {j}))

/-- Adding epsilon times the target to a finite reference increases
generalized KL by at most epsilon, when the target has mass one. -/
theorem finite_kl_add_target_right_le (mu nu : Measure ι)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hnu : ∀ i, nu {i} ≠ 0) (eps : ℝ≥0) :
    klDiv mu (nu+(eps : ℝ≥0∞) • mu) ≤ klDiv mu nu+(eps : ℝ≥0∞) := by
  let _ : IsFiniteMeasure ((eps : ℝ≥0∞) • mu) := mu.smul_finite ENNReal.coe_ne_top
  let theta := nu+(eps : ℝ≥0∞) • mu
  have hp : ∀ i, theta {i} ≠ 0 := by
    intro i hi
    change nu {i}+(eps : ℝ≥0∞)*mu {i} = 0 at hi
    exact hnu i (add_eq_zero.mp hi).1
  have ht : ∀ E : Set ι, theta.real E = nu.real E+(eps : ℝ)*mu.real E := by
    intro E
    change (nu+(eps : ℝ≥0∞) • mu).real E = _
    rw [measureReal_add_apply]
    simp only [measureReal_def,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal]
  have hsum : (∑ i, mu.real {i}*Real.log (mu.real {i}/theta.real {i})) ≤
      ∑ i, mu.real {i}*Real.log (mu.real {i}/nu.real {i}) := by
    apply sum_le_sum
    intro i _
    by_cases hz : mu.real {i} = 0
    · simp only [hz,zero_mul,le_refl]
    · have hm : 0 < mu.real {i} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
      have hv : 0 < nu.real {i} := ENNReal.toReal_pos (hnu i) (measure_ne_top nu {i})
      have htv : nu.real {i} ≤ theta.real {i} := by
        rw [ht]
        exact le_add_of_nonneg_right (mul_nonneg eps.coe_nonneg hm.le)
      apply mul_le_mul_of_nonneg_left _ hm.le
      apply Real.log_le_log (div_pos hm (hv.trans_le htv))
      exact div_le_div_of_nonneg_left hm.le hv htv
  rw [finite_kl_eq_ofReal_sum mu theta hp,finite_kl_eq_ofReal_sum mu nu hnu]
  rw [ht Set.univ,probReal_univ,probReal_univ,mul_one]
  have hnonneg : 0 ≤ (∑ i, mu.real {i}*Real.log (mu.real {i}/nu.real {i}))+1-1 := by
    have he := finite_kl_toReal_eq_sum mu nu hnu
    simp only [probReal_univ] at he
    rw [← he]
    exact ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_add hnonneg eps.coe_nonneg]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hsum]

end LatinonEntropy

#print axioms LatinonEntropy.finite_atom_cost_nonneg
#print axioms LatinonEntropy.finite_kl_eq_sum_atom_cost
#print axioms LatinonEntropy.finite_atom_cost_le_kl
#print axioms LatinonEntropy.finite_kl_add_target_right_le
