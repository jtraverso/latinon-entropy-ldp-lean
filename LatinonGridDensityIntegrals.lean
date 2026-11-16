module

public import CubeObservationDensity
public import LatinonDyadicGridKL

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem coordinate_grid_fiber_ae (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ p ∂W.measure, ∀ b : GridBoxIndex n,
      coordinateGridIndex n hn p = b ↔ p ∈ latinonGridBox b := by
  filter_upwards [latinonGridBox_cover W hn] with p hp
  obtain ⟨c,hc⟩ := hp
  rw [coordinateGridIndex_of_mem hn hc.1.1 hc.1.2 hc.2]
  intro b
  constructor
  · intro he
    exact he ▸ hc
  · intro hb
    by_contra hne
    exact Set.disjoint_left.mp (latinonGridBox_disjoint hn c b hne) hc hb

theorem coordinate_grid_restricted_atom (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (E : Set LatinonPoint) (b : GridBoxIndex n) :
    ((W.measure.restrict E).map (coordinateGridIndex n hn)) {b} =
      W.measure (E ∩ latinonGridBox b) := by
  rw [Measure.map_apply (coordinateGridIndex_measurable n hn) (measurableSet_singleton b),
    Measure.restrict_apply ((measurableSet_singleton b).preimage (coordinateGridIndex_measurable n hn))]
  apply measure_congr
  filter_upwards [coordinate_grid_fiber_ae W hn] with p hp
  apply propext
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff]
  exact (and_congr (hp b) Iff.rfl).trans and_comm

theorem uniform_coordinate_grid_atom_ne_zero {n : ℕ} (hn : 0 < n) (b : GridBoxIndex n) :
    (uniformLatinonMeasure.measure.map (coordinateGridIndex n hn)) {b} ≠ 0 := by
  intro hz
  have he := congrArg ENNReal.toReal hz
  rw [coordinate_grid_map_atom uniformLatinonMeasure hn] at he
  change uniformLatinonMeasure.measure.real (latinonGridBox b) = 0 at he
  rw [uniform_latinon_grid_box_mass hn] at he
  exact (pow_pos (div_pos zero_lt_one (Nat.cast_pos.mpr hn : (0 : ℝ) < n)) 3).ne' he

theorem coordinate_grid_rn_real (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) (b : GridBoxIndex n) :
    (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
      (unitCubeVolume.map (coordinateGridIndex n hn))) b).toReal =
        (n : ℝ)^3*W.measure.real (latinonGridBox b) := by
  change (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
    (uniformLatinonMeasure.measure.map (coordinateGridIndex n hn))) b).toReal = _
  rw [finite_rnDeriv_eq_ratio _ _ (uniform_coordinate_grid_atom_ne_zero hn),ENNReal.toReal_div]
  have hm : ∀ V : LatinonMeasure, (V.measure.map (coordinateGridIndex n hn)).real {b} =
      V.measure.real (latinonGridBox b) := fun V => congrArg ENNReal.toReal (coordinate_grid_map_atom V hn b)
  change (W.measure.map (coordinateGridIndex n hn)).real {b}/
    (uniformLatinonMeasure.measure.map (coordinateGridIndex n hn)).real {b} = _
  rw [hm W,hm uniformLatinonMeasure,uniform_latinon_grid_box_mass hn]
  simp only [one_div,inv_pow,div_inv_eq_mul,mul_comm]

/-- The ACTUAL Latinon grid coarsening integrates the actual observation
density. This identifies the density approximation with C3's grid centre. -/
theorem grid_coarsening_real_box_eq_observation_integral (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (S T U : Set I) :
    (gridTensorMeasure (latinonGridTensor W (n := n))).real ((S ×ˢ T) ×ˢ U) =
      ∫ p in (S ×ˢ T) ×ˢ U, cubeObservationDensity W.measure hn p ∂unitCubeVolume := by
  let E := (S ×ˢ T) ×ˢ U
  let q : GridBoxIndex n → ℝ := fun b =>
    (((W.measure.map (coordinateGridIndex n hn)).rnDeriv
      (unitCubeVolume.map (coordinateGridIndex n hn))) b).toReal
  have hi := integral_map_of_stronglyMeasurable (μ := unitCubeVolume.restrict E)
    (coordinateGridIndex_measurable n hn) (measurable_of_countable q).stronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at hi
  simp only [smul_eq_mul] at hi
  have hm : ∀ b : GridBoxIndex n,
      ((unitCubeVolume.restrict E).map (coordinateGridIndex n hn)).real {b} =
        unitCubeVolume.real (E ∩ latinonGridBox b) := fun b =>
    congrArg ENNReal.toReal (coordinate_grid_restricted_atom uniformLatinonMeasure hn E b)
  simp_rw [hm] at hi
  have hq : ∀ b : GridBoxIndex n, q b = (n : ℝ)^3*W.measure.real (latinonGridBox b) :=
    fun b => coordinate_grid_rn_real W hn b
  have hqsum : (∑ b : GridBoxIndex n, unitCubeVolume.real (E ∩ latinonGridBox b)*q b) =
      ∑ b : GridBoxIndex n, unitCubeVolume.real (E ∩ latinonGridBox b)*
        ((n : ℝ)^3*W.measure.real (latinonGridBox b)) := by
    apply sum_congr rfl
    intro b _
    rw [hq b]
  rw [hqsum] at hi
  have hv : ∀ b : GridBoxIndex n, unitCubeVolume.real (E ∩ latinonGridBox b) =
      (volume : Measure I).real (S ∩ lebesgueGridCell b.1.1)*
        volume.real (T ∩ lebesgueGridCell b.1.2)*volume.real (U ∩ lebesgueGridCell b.2) := by
    intro b
    dsimp only [E,latinonGridBox]
    rw [Set.prod_inter_prod,Set.prod_inter_prod,measureReal_prod_prod,measureReal_prod_prod]
  simp_rw [hv,Fintype.sum_prod_type] at hi
  change (∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n,
      (volume : Measure I).real (S ∩ lebesgueGridCell x)*
        volume.real (T ∩ lebesgueGridCell y)*volume.real (U ∩ lebesgueGridCell z)*
          ((n : ℝ)^3*W.measure.real (latinonGridBox ((x,y),z)))) =
    ∫ p in (S ×ˢ T) ×ˢ U, cubeObservationDensity W.measure hn p ∂unitCubeVolume at hi
  rw [← hi,gridTensorMeasure_real_box _ (latinon_grid_tensor_nonneg W)]
  simp only [mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  dsimp only [latinonGridTensor,latinonGridBox]
  ring

end LatinonEntropy

#print axioms LatinonEntropy.coordinate_grid_fiber_ae
#print axioms LatinonEntropy.coordinate_grid_restricted_atom
#print axioms LatinonEntropy.uniform_coordinate_grid_atom_ne_zero
#print axioms LatinonEntropy.coordinate_grid_rn_real
#print axioms LatinonEntropy.grid_coarsening_real_box_eq_observation_integral
