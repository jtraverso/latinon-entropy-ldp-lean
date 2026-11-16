module

public import FiniteKLPerturbation
public import KLGeneratingObservations
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Filter Topology
open scoped Classical ENNReal NNReal

/-- Positive-reference finite observations recover KL also for singular
probability measures. The singular case is proved by reference perturbation
and a binary observation of a null-reference set. -/
theorem klDiv_eq_iSup_finite_generating_maps
    {α : Type*} [MeasurableSpace α] (mu nu : Measure α)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {β : ℕ → Type*} [∀ k, Fintype (β k)] [∀ k, MeasurableSpace (β k)]
    [∀ k, MeasurableSingletonClass (β k)]
    (g : ∀ k, α → β k) (hg : ∀ k, Measurable (g k))
    (hmono : Monotone (fun k => (inferInstance : MeasurableSpace (β k)).comap (g k)))
    (hgen : (⨆ k, (inferInstance : MeasurableSpace (β k)).comap (g k)) =
      (inferInstance : MeasurableSpace α))
    (hpositive : ∀ k i, (nu.map (g k)) {i} ≠ 0) :
    klDiv mu nu = ⨆ k, klDiv (mu.map (g k)) (nu.map (g k)) := by
  by_cases hac : mu ≪ nu
  · exact klDiv_eq_iSup_generating_maps_of_ac mu nu hac g hg hmono hgen
  let S := ⨆ k, klDiv (mu.map (g k)) (nu.map (g k))
  have htop : S = ⊤ := by
    by_contra hS
    have hex : ∃ E : Set α, MeasurableSet E ∧ nu E = 0 ∧ mu E ≠ 0 := by
      by_contra! h
      exact hac (Measure.AbsolutelyContinuous.mk fun E hE hzero => h E hE hzero)
    obtain ⟨E,hE,hnE,hmE⟩ := hex
    let m := mu.real E
    have hm : 0 < m := ENNReal.toReal_pos hmE (measure_ne_top mu E)
    let T := (S.toReal+3+m)/m
    have hT : 0 < T := div_pos (by linarith only [ENNReal.toReal_nonneg (a := S),hm]) hm
    let eps : ℝ≥0 := ⟨Real.exp (-T),(Real.exp_pos _).le⟩
    have heps : 0 < (eps : ℝ) := Real.exp_pos _
    have heps1 : (eps : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT.le)
    have heps0 : (eps : ℝ≥0∞) ≠ 0 := by exact_mod_cast heps.ne'
    let _ : IsFiniteMeasure ((eps : ℝ≥0∞) • mu) := mu.smul_finite ENNReal.coe_ne_top
    let theta := nu+(eps : ℝ≥0∞) • mu
    have hac' : mu ≪ theta :=
      (Measure.AbsolutelyContinuous.rfl.smul_right heps0).add_right' nu
    have hupper : klDiv mu theta ≤ S+(eps : ℝ≥0∞) := by
      rw [klDiv_eq_iSup_generating_maps_of_ac mu theta hac' g hg hmono hgen]
      apply iSup_le
      intro k
      let _ : IsProbabilityMeasure (mu.map (g k)) := ⟨by
        rw [Measure.map_apply (hg k) MeasurableSet.univ]
        simp only [Set.preimage_univ,measure_univ]⟩
      let _ : IsProbabilityMeasure (nu.map (g k)) := ⟨by
        rw [Measure.map_apply (hg k) MeasurableSet.univ]
        simp only [Set.preimage_univ,measure_univ]⟩
      change klDiv (mu.map (g k)) ((nu+(eps : ℝ≥0∞) • mu).map (g k)) ≤ _
      rw [Measure.map_add _ _ (hg k),Measure.map_smul _ (hg k).aemeasurable]
      exact (finite_kl_add_target_right_le _ _ (hpositive k) eps).trans
        (add_le_add (le_iSup (fun j => klDiv (mu.map (g j)) (nu.map (g j))) k) le_rfl)
    let B : α → Bool := fun x => if x ∈ E then true else false
    have hB : Measurable B := measurable_const.ite hE measurable_const
    have htrue : B ⁻¹' {true} = E := by ext x; simp [B]
    have hfalse : B ⁻¹' {false} = Eᶜ := by ext x; simp [B]
    have hncomp : nu Eᶜ = 1 := by rw [measure_compl hE (measure_ne_top nu E),hnE,measure_univ,tsub_zero]
    have hposB : ∀ b : Bool, (theta.map B) {b} ≠ 0 := by
      intro b
      rw [Measure.map_apply hB (measurableSet_singleton b)]
      cases b with
      | false =>
        rw [hfalse]
        change nu Eᶜ+(eps : ℝ≥0∞)*mu Eᶜ ≠ 0
        rw [hncomp]
        exact fun hz => one_ne_zero (add_eq_zero.mp hz).1
      | true =>
        rw [htrue]
        change nu E+(eps : ℝ≥0∞)*mu E ≠ 0
        rw [hnE,zero_add]
        exact mul_ne_zero heps0 hmE
    have hmuB : (mu.map B).real {true} = m := by
      rw [measureReal_def,Measure.map_apply hB (measurableSet_singleton true),htrue]
      rfl
    have hthetaB : (theta.map B).real {true} = (eps : ℝ)*m := by
      rw [measureReal_def,Measure.map_apply hB (measurableSet_singleton true),htrue]
      change (nu E+(eps : ℝ≥0∞)*mu E).toReal = _
      rw [hnE,zero_add,ENNReal.toReal_mul,ENNReal.coe_toReal]
      rfl
    have hlog : Real.log (m/((eps : ℝ)*m)) = T := by
      have he : m/((eps : ℝ)*m) = 1/(eps : ℝ) := by field_simp
      rw [he,Real.log_div one_ne_zero heps.ne',Real.log_one]
      change 0-Real.log (Real.exp (-T)) = T
      rw [Real.log_exp]
      ring
    have hlower := finite_atom_cost_le_kl (mu.map B) (theta.map B) hposB true
    rw [hmuB,hthetaB,hlog] at hlower
    have hboth := hlower.trans ((klDiv_map_le mu theta hB).trans hupper)
    have hreal : S+(eps : ℝ≥0∞) = ENNReal.ofReal (S.toReal+(eps : ℝ)) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg eps.coe_nonneg,
        ENNReal.ofReal_toReal hS,ENNReal.ofReal_coe_nnreal]
    rw [hreal] at hboth
    have hbound := (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg ENNReal.toReal_nonneg eps.coe_nonneg)).mp hboth
    have hmul : m*T = S.toReal+3+m := by
      dsimp only [T]
      exact mul_div_cancel₀ _ hm.ne'
    rw [hmul] at hbound
    have hprod : 0 ≤ (eps : ℝ)*m := mul_nonneg heps.le hm.le
    linarith only [hbound,hprod,heps1]
  rw [klDiv_of_not_ac hac]
  exact htop.symm

end LatinonEntropy

#print axioms LatinonEntropy.klDiv_eq_iSup_finite_generating_maps
