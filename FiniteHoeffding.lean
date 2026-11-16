module

public import FiniteAverages
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory ProbabilityTheory

/-- Mathlib's Hoeffding lemma specialized to explicit finite weights. -/
theorem finite_centered_hoeffding {I : Type*} [Fintype I]
    (p g : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (hg : ∀ i, |g i| ≤ 1) (t : ℝ) :
    (∑ i, p i * Real.exp (t * (g i - ∑ j, p j * g j))) ≤ Real.exp (t^2/2) := by
  classical
  let : MeasurableSpace I := ⊤
  have hsum : (∑ i, ENNReal.ofReal (p i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i),hmass,ENNReal.ofReal_one]
  let P : PMF I := PMF.ofFintype (fun i => ENNReal.ofReal (p i)) hsum
  have he : ∀ f : I → ℝ, (∫ i, f i ∂P.toMeasure) = ∑ i, p i * f i := by
    intro f
    rw [PMF.integral_eq_sum]
    simp only [P,PMF.ofFintype_apply,smul_eq_mul]
    simp_rw [ENNReal.toReal_ofReal (hp _)]
  have hm : AEMeasurable g P.toMeasure := (measurable_of_finite g).aemeasurable
  have hb : ∀ᵐ i ∂P.toMeasure, g i ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun i => abs_le.mp (hg i))
  have hsub := hasSubgaussianMGF_of_mem_Icc hm hb
  have h := hsub.mgf_le t
  simp only [mgf,he] at h
  norm_num at h
  exact h

theorem finite_log_mgf_le {I : Type*} [Fintype I]
    (p g : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (hg : ∀ i, |g i| ≤ 1) (t : ℝ)
    (hpos : 0 < ∑ i, p i * Real.exp (t*g i)) :
    Real.log (∑ i, p i * Real.exp (t*g i)) ≤ t * (∑ i, p i * g i) + t^2/2 := by
  have h := finite_centered_hoeffding p g hp hmass hg t
  have he : (∑ i, p i * Real.exp (t * (g i - ∑ j, p j * g j))) =
      (∑ i, p i * Real.exp (t*g i)) * Real.exp (-t*(∑ j, p j*g j)) := by
    simp only [mul_sub,Real.exp_sub,neg_mul,Real.exp_neg,div_eq_mul_inv,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  rw [he] at h
  have hlog := Real.log_le_log (mul_pos hpos (Real.exp_pos _)) h
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp] at hlog
  linarith

end LatinonEntropy

#print axioms LatinonEntropy.finite_centered_hoeffding
#print axioms LatinonEntropy.finite_log_mgf_le
