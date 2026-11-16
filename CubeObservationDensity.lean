module

public import ConditionalGridApproximation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def cubeObservationDensity (mu : Measure ((I × I) × I)) {n : ℕ} (hn : 0 < n) (p : (I × I) × I) : ℝ :=
  (((mu.map (coordinateGridIndex n hn)).rnDeriv
    (unitCubeVolume.map (coordinateGridIndex n hn))) (coordinateGridIndex n hn p)).toReal

theorem cubeObservationDensity_nonneg (mu : Measure ((I × I) × I)) {n : ℕ} (hn : 0 < n) (p) :
    0 ≤ cubeObservationDensity mu hn p := ENNReal.toReal_nonneg

theorem cubeObservationDensity_ae_condExp (mu : Measure ((I × I) × I)) [IsFiniteMeasure mu]
    (hac : mu ≪ unitCubeVolume) {n : ℕ} (hn : 0 < n) :
    cubeObservationDensity mu hn =ᵐ[unitCubeVolume]
      unitCubeVolume[fun p => (mu.rnDeriv unitCubeVolume p).toReal | cubeGridSigma n hn] :=
  toReal_rnDeriv_map hac (coordinateGridIndex_measurable n hn)

theorem cubeObservationDensity_integrable (mu : Measure ((I × I) × I)) [IsFiniteMeasure mu]
    (hac : mu ≪ unitCubeVolume) {n : ℕ} (hn : 0 < n) :
    Integrable (cubeObservationDensity mu hn) unitCubeVolume :=
  integrable_condExp.congr (cubeObservationDensity_ae_condExp mu hac hn).symm

/-- The actual finite-observation densities converge to the actual RN
density along ALL grid sizes. Absolute continuity is explicit. -/
theorem exists_all_sizes_observation_density_L1 (mu : Measure ((I × I) × I)) [IsFiniteMeasure mu]
    (hac : mu ≪ unitCubeVolume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      (∫ p, |(mu.rnDeriv unitCubeVolume p).toReal-
        cubeObservationDensity mu (hN.trans_le hn) p| ∂unitCubeVolume) ≤ eps := by
  obtain ⟨N,hN,hconv⟩ := exists_all_sizes_cube_condExp_L1
    (fun p => (mu.rnDeriv unitCubeVolume p).toReal) Measure.integrable_toReal_rnDeriv eps heps
  refine ⟨N,hN,?_⟩
  intro n hn
  have he := cubeObservationDensity_ae_condExp mu hac (hN.trans_le hn)
  have hi : (∫ p, |(mu.rnDeriv unitCubeVolume p).toReal-cubeObservationDensity mu (hN.trans_le hn) p| ∂unitCubeVolume) =
      ∫ p, |(mu.rnDeriv unitCubeVolume p).toReal-
        (unitCubeVolume[fun p => (mu.rnDeriv unitCubeVolume p).toReal | cubeGridSigma n (hN.trans_le hn)]) p| ∂unitCubeVolume := by
    apply integral_congr_ae
    filter_upwards [he] with p hp
    rw [hp]
  rw [hi]
  exact hconv n hn

end LatinonEntropy

#print axioms LatinonEntropy.cubeObservationDensity_nonneg
#print axioms LatinonEntropy.cubeObservationDensity_ae_condExp
#print axioms LatinonEntropy.cubeObservationDensity_integrable
#print axioms LatinonEntropy.exists_all_sizes_observation_density_L1
