module

public import CubeGridL1Approximation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Conditional averaging is within twice the L1 error of any integrable
step function measurable for the observation sigma-algebra. -/
theorem condExp_L1_le_twice_step_error {α : Type*} [m0 : MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] (m : MeasurableSpace α) (hm : m ≤ m0)
    (f g : α → ℝ) (hf : Integrable f mu) (hg : Integrable g mu) (hgm : StronglyMeasurable[m] g) :
    (∫ x, |f x-(mu[f | m]) x| ∂mu) ≤ 2*(∫ x, |f x-g x| ∂mu) := by
  have hCG := condExp_of_stronglyMeasurable hm hgm hg
  have he := condExp_sub hf hg m
  rw [hCG] at he
  have hdiff : Integrable (fun x => |f x-(mu[f | m]) x|) mu := (hf.sub integrable_condExp).abs
  have hfg : Integrable (fun x => |f x-g x|) mu := (hf.sub hg).abs
  have hcond : Integrable (fun x => |(mu[f-g | m]) x|) mu := integrable_condExp.abs
  have hb : (∫ x, |f x-(mu[f | m]) x| ∂mu) ≤
      (∫ x, |f x-g x| ∂mu)+(∫ x, |(mu[f-g | m]) x| ∂mu) := by
    rw [← integral_add hfg hcond]
    apply integral_mono_ae hdiff (hfg.add hcond)
    filter_upwards [he] with x hx
    dsimp only [Pi.add_apply]
    have habs : |g x-(mu[f | m]) x| = |(mu[f-g | m]) x| := by
      rw [hx,Pi.sub_apply]
      exact abs_sub_comm _ _
    exact (abs_sub_le (f x) (g x) ((mu[f | m]) x)).trans_eq (congrArg (fun z => |f x-g x|+z) habs)
  have hc := integral_abs_condExp_le (μ := mu) (m := m) (f-g)
  change (∫ x, |(mu[f-g | m]) x| ∂mu) ≤ (∫ x, |f x-g x| ∂mu) at hc
  linarith only [hb,hc]

@[instance_reducible] def cubeGridSigma (n : ℕ) (hn : 0 < n) : MeasurableSpace ((I × I) × I) :=
  (inferInstance : MeasurableSpace ((Fin n × Fin n) × Fin n)).comap (coordinateGridIndex n hn)

theorem cubeGridSigma_le (n : ℕ) (hn : 0 < n) :
    cubeGridSigma n hn ≤ (inferInstance : MeasurableSpace ((I × I) × I)) :=
  (coordinateGridIndex_measurable n hn).comap_le

/-- Actual cube conditional averages converge in L1 along ALL grid sizes.
The approximation hypothesis is discharged by continuous L1 density. -/
theorem exists_all_sizes_cube_condExp_L1 (f : (I × I) × I → ℝ)
    (hf : Integrable f unitCubeVolume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (∫ p, |f p-(unitCubeVolume[f | cubeGridSigma n (hN.trans_le hn)]) p| ∂unitCubeVolume) ≤ eps := by
  obtain ⟨N,hN,hstep⟩ := exists_all_sizes_cube_grid_step_L1 f hf (eps/2) (half_pos heps)
  refine ⟨N,hN,?_⟩
  intro n hn
  obtain ⟨a,ha,herr⟩ := hstep n hn
  have hsm : StronglyMeasurable[cubeGridSigma n (hN.trans_le hn)]
      (fun p => a (coordinateGridIndex n (hN.trans_le hn) p)) :=
    ((measurable_of_countable a).comp (comap_measurable (coordinateGridIndex n (hN.trans_le hn)))).stronglyMeasurable
  have hb := condExp_L1_le_twice_step_error unitCubeVolume (cubeGridSigma n (hN.trans_le hn))
    (cubeGridSigma_le n (hN.trans_le hn)) f _ hf ha hsm
  linarith only [hb,herr]

end LatinonEntropy

#print axioms LatinonEntropy.condExp_L1_le_twice_step_error
#print axioms LatinonEntropy.cubeGridSigma_le
#print axioms LatinonEntropy.exists_all_sizes_cube_condExp_L1
