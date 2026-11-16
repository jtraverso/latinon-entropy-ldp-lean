module

public import DyadicCubeFiltration
public import KLGeneratingObservations
public import LatinonGridKL
public import BoundedLatinonGridProfile

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Finset
open scoped Classical unitInterval ENNReal

theorem coordinate_grid_map_atom (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (b : GridBoxIndex n) :
    (W.measure.map (coordinateGridIndex n hn)) {b} = W.measure (latinonGridBox b) := by
  let z : Fin n := ⟨0,hn⟩
  have he : coordinateGridIndex n hn =ᵐ[W.measure] finiteCellIndex latinonGridBox ((z,z),z) := by
    filter_upwards [latinonGridBox_cover W hn] with p hp
    obtain ⟨c,hc⟩ := hp
    rw [coordinateGridIndex_of_mem hn hc.1.1 hc.1.2 hc.2,
      finiteCellIndex_of_mem latinonGridBox ((z,z),z) (latinonGridBox_disjoint hn) hc]
  rw [Measure.map_congr he]
  exact finiteCellIndex_map_cell W.measure latinonGridBox ((z,z),z)
    latinonGridBox_measurable (latinonGridBox_disjoint hn) (latinonGridBox_cover W hn) b

theorem latinon_coordinate_grid_kl (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    klDiv (W.measure.map (coordinateGridIndex n hn))
      (uniformLatinonMeasure.measure.map (coordinateGridIndex n hn)) =
        ENNReal.ofReal (-latinonGridTableEntropy W n) := by
  let g := coordinateGridIndex n hn
  have hg : Measurable g := coordinateGridIndex_measurable n hn
  let _ : IsProbabilityMeasure (W.measure.map g) := ⟨by
    rw [Measure.map_apply hg MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]⟩
  let _ : IsProbabilityMeasure (uniformLatinonMeasure.measure.map g) := ⟨by
    rw [Measure.map_apply hg MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]⟩
  have hp : ∀ b : GridBoxIndex n, (uniformLatinonMeasure.measure.map g) {b} ≠ 0 := by
    intro b hz
    have hr := congrArg ENNReal.toReal hz
    change (uniformLatinonMeasure.measure.map (coordinateGridIndex n hn)).real {b} = 0 at hr
    rw [measureReal_def,coordinate_grid_map_atom uniformLatinonMeasure hn] at hr
    change uniformLatinonMeasure.measure.real (latinonGridBox b) = 0 at hr
    rw [uniform_latinon_grid_box_mass hn] at hr
    exact (pow_pos (div_pos zero_lt_one (Nat.cast_pos.mpr hn : (0 : ℝ) < n)) 3).ne' hr
  rw [finite_probability_kl_eq_neg_table (W.measure.map g) (uniformLatinonMeasure.measure.map g) hp]
  have hm : ∀ (V : LatinonMeasure) (b : GridBoxIndex n),
      (V.measure.map g).real {b} = V.measure.real (latinonGridBox b) := fun V b =>
    congrArg ENNReal.toReal (coordinate_grid_map_atom V hn b)
  simp_rw [hm]
  rfl

/-- The reverse variational inequality is derived from the actual dyadic
observations and exact Borel generation, rather than assumed for profiles. -/
theorem latinon_rate_eq_iSup_dyadic_of_ac (W : LatinonMeasure)
    (hac : W.measure ≪ uniformLatinonMeasure.measure) :
    latinonRate W = ⨆ k, ENNReal.ofReal (-latinonGridTableEntropy W (dyadicGridSize k)) := by
  change klDiv W.measure uniformLatinonMeasure.measure = _
  rw [klDiv_eq_iSup_generating_maps_of_ac W.measure uniformLatinonMeasure.measure hac
    dyadicCubeIndex (fun k => coordinateGridIndex_measurable _ (dyadicGridSize_pos k))
    dyadicCubeSigma_monotone dyadicCubeSigma_iSup]
  congr 1
  funext k
  exact latinon_coordinate_grid_kl W (dyadicGridSize_pos k)

theorem bounded_latinon_absolutelyContinuous (W : LatinonMeasure) (a b : ℝ)
    (h : HasLatinonDensityBounds W a b) : W.measure ≪ uniformLatinonMeasure.measure := by
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hzero
  have hr : uniformLatinonMeasure.measure.real E = 0 := congrArg ENNReal.toReal hzero
  have hu := (h E hE).2
  rw [hr,mul_zero] at hu
  exact (measureReal_eq_zero_iff).mp (le_antisymm hu measureReal_nonneg)

theorem bounded_latinon_rate_eq_iSup_dyadic (W : LatinonMeasure) (a b : ℝ)
    (h : HasLatinonDensityBounds W a b) :
    latinonRate W = ⨆ k, ENNReal.ofReal (-latinonGridTableEntropy W (dyadicGridSize k)) :=
  latinon_rate_eq_iSup_dyadic_of_ac W (bounded_latinon_absolutelyContinuous W a b h)

end LatinonEntropy

#print axioms LatinonEntropy.coordinate_grid_map_atom
#print axioms LatinonEntropy.latinon_coordinate_grid_kl
#print axioms LatinonEntropy.latinon_rate_eq_iSup_dyadic_of_ac
#print axioms LatinonEntropy.bounded_latinon_absolutelyContinuous
#print axioms LatinonEntropy.bounded_latinon_rate_eq_iSup_dyadic
