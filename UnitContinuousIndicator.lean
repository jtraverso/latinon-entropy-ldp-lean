module

public import UnitGridL1Approximation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem abs_sub_unit_clip_le (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |a-max 0 (min 1 b)| ≤ |a-b| := by
  obtain ⟨ha0,ha1⟩ := ha
  by_cases hb0 : b ≤ 0
  · rw [min_eq_right (hb0.trans zero_le_one),max_eq_left hb0,
      sub_zero,abs_of_nonneg ha0,abs_of_nonneg (by linarith : 0 ≤ a-b)]
    linarith
  · by_cases hb1 : 1 ≤ b
    · rw [min_eq_left hb1,max_eq_right zero_le_one,
        abs_of_nonpos (by linarith : a-1 ≤ 0),abs_of_nonpos (by linarith : a-b ≤ 0)]
      linarith
    · rw [min_eq_right (le_of_not_ge hb1),max_eq_right (le_of_not_ge hb0)]

/-- Continuous [0,1]-valued approximations to any measurable indicator.
This supplies the missing arbitrary-set approximation in the weak-limit argument. -/
theorem exists_continuous_unit_indicator_L1 (S : Set I) (hS : MeasurableSet S)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ g : I → ℝ, Continuous g ∧ (∀ u, g u ∈ Set.Icc (0 : ℝ) 1) ∧
      (∫ u, |S.indicator (fun _ => (1 : ℝ)) u-g u|) ≤ eps := by
  let f : I → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f volume := (integrable_const (1 : ℝ)).indicator hS
  have hf01 (u : I) : f u ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hu : u ∈ S <;> simp [f,hu]
  obtain ⟨g,happrox,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le heps
  let c : I → ℝ := fun u => max 0 (min 1 (g u))
  have hc : Continuous c := continuous_const.max (continuous_const.min g.continuous)
  have hcb (u : I) : c u ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  have hci : Integrable c volume := Integrable.of_mem_Icc 0 1 hc.measurable.aemeasurable
    (ae_of_all volume hcb)
  refine ⟨c,hc,hcb,?_⟩
  calc
    (∫ u, |f u-c u|) ≤ ∫ u, |f u-g u| :=
      integral_mono (hf.sub hci).abs (hf.sub hgi).abs
        (fun u => abs_sub_unit_clip_le (f u) (g u) (hf01 u))
    _ ≤ eps := by simpa only [Real.norm_eq_abs] using happrox

end LatinonEntropy

#print axioms LatinonEntropy.abs_sub_unit_clip_le
#print axioms LatinonEntropy.exists_continuous_unit_indicator_L1
