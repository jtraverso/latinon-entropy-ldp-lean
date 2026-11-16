module

public import LatinonGridDensityIntegrals
public import DensityMassComparison

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem grid_coarsening_measureCut_le_L1 (W : LatinonMeasure)
    (hac : W.measure ≪ unitCubeVolume) {n : ℕ} (hn : 0 < n) :
    measureCut W.measure (gridTensorMeasure (latinonGridTensor W (n := n))) ≤
      ∫ p, |(W.measure.rnDeriv unitCubeVolume p).toReal-cubeObservationDensity W.measure hn p| ∂unitCubeVolume := by
  apply cutValueSup_le
  intro B
  change |W.measure.real ((B.rows ×ˢ B.cols) ×ˢ B.symbols)-
    (gridTensorMeasure (latinonGridTensor W (n := n))).real ((B.rows ×ˢ B.cols) ×ˢ B.symbols)| ≤ _
  rw [grid_coarsening_real_box_eq_observation_integral W hn B.rows B.cols B.symbols]
  exact abs_mass_sub_density_integral_le W.measure unitCubeVolume hac _
    (cubeObservationDensity_integrable W.measure hac hn) _

/-- The ACTUAL C3 grid distributions approximate each absolutely
continuous Latinon in distribution cut,for every sufficiently large size. -/
theorem exists_all_sizes_grid_distribution_cut (W : LatinonMeasure)
    (hac : W.measure ≪ unitCubeVolume) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (_hN : 0 < N), ∀ (n : ℕ) (_hn : N ≤ n),
      measureCut W.measure (gridTensorMeasure (latinonGridTensor W (n := n))) ≤ eps := by
  obtain ⟨N,hN,hconv⟩ := exists_all_sizes_observation_density_L1 W.measure hac eps heps
  refine ⟨N,hN,?_⟩
  intro n hn
  exact (grid_coarsening_measureCut_le_L1 W hac (hN.trans_le hn)).trans (hconv n hn)

theorem exists_finite_rate_grid_distribution_cut (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (_hN : 0 < N), ∀ (n : ℕ) (_hn : N ≤ n),
      measureCut W.measure (gridTensorMeasure (latinonGridTensor W (n := n))) ≤ eps := by
  apply exists_all_sizes_grid_distribution_cut W _ eps heps
  exact (InformationTheory.klDiv_ne_top_iff.mp hfinite).1

end LatinonEntropy

#print axioms LatinonEntropy.grid_coarsening_measureCut_le_L1
#print axioms LatinonEntropy.exists_all_sizes_grid_distribution_cut
#print axioms LatinonEntropy.exists_finite_rate_grid_distribution_cut
