module

public import LatinonDyadicConsequences
public import KLFiniteGeneratingObservations

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Filter Topology Finset
open scoped Classical ENNReal unitInterval

/-- Exact variational identity for every Latinon, with singular measures
and infinite divergence included. The observations are the actual grids. -/
theorem latinon_rate_eq_iSup_dyadic (W : LatinonMeasure) :
    latinonRate W = ⨆ k, ENNReal.ofReal (-latinonGridTableEntropy W (dyadicGridSize k)) := by
  have hp : ∀ k b, (uniformLatinonMeasure.measure.map (dyadicCubeIndex k)) {b} ≠ 0 := by
    intro k b hz
    have he := congrArg ENNReal.toReal hz
    change (uniformLatinonMeasure.measure.map
      (coordinateGridIndex (dyadicGridSize k) (dyadicGridSize_pos k))).real {b} = 0 at he
    rw [measureReal_def,coordinate_grid_map_atom uniformLatinonMeasure (dyadicGridSize_pos k)] at he
    change uniformLatinonMeasure.measure.real (latinonGridBox b) = 0 at he
    rw [uniform_latinon_grid_box_mass (dyadicGridSize_pos k)] at he
    exact (pow_pos (div_pos zero_lt_one
      (Nat.cast_pos.mpr (dyadicGridSize_pos k) : (0 : ℝ) < dyadicGridSize k)) 3).ne' he
  change klDiv W.measure uniformLatinonMeasure.measure = _
  rw [klDiv_eq_iSup_finite_generating_maps W.measure uniformLatinonMeasure.measure dyadicCubeIndex
    (fun k => coordinateGridIndex_measurable _ (dyadicGridSize_pos k))
    dyadicCubeSigma_monotone dyadicCubeSigma_iSup hp]
  congr 1
  funext k
  exact latinon_coordinate_grid_kl W (dyadicGridSize_pos k)

theorem exists_dyadic_grid_divergence_gt (W : LatinonMeasure) (t : ℝ)
    (ht : ENNReal.ofReal t < latinonRate W) :
    ∃ k, t < -latinonGridTableEntropy W (dyadicGridSize k) := by
  rw [latinon_rate_eq_iSup_dyadic W] at ht
  obtain ⟨k,hk⟩ := lt_iSup_iff.mp ht
  exact ⟨k,(ENNReal.ofReal_lt_ofReal_iff'.mp hk).1⟩

/-- Lower semicontinuity uses the full order-sensitive pseudometric.
No density, finite-rate or alignment hypothesis is supplied by the caller. -/
theorem latinon_rate_lowerSemicontinuous : LowerSemicontinuous latinonRate := by
  intro W y hy
  rw [latinon_rate_eq_iSup_dyadic W] at hy
  obtain ⟨k,hk⟩ := lt_iSup_iff.mp hy
  have hr := ENNReal.toReal_lt_of_lt_ofReal hk
  let E := latinonGridTableEntropy W (dyadicGridSize k)
  let eta := (-E-y.toReal)/2
  have heta : 0 < eta := by dsimp only [eta,E]; linarith only [hr]
  obtain ⟨delta,hd,hlocal⟩ := exists_latinon_grid_rate_neighborhood W (dyadicGridSize_pos k) eta heta
  apply Filter.mem_of_superset (Metric.ball_mem_nhds W hd)
  intro V hV
  apply lt_of_lt_of_le _ (hlocal V hV)
  apply (ENNReal.lt_ofReal_iff_toReal_lt hk.ne_top).mpr
  dsimp only [eta,E]
  linarith only [hr]

theorem latinon_rate_eq_of_dist_zero (W V : LatinonMeasure) (h : dist W V = 0) :
    latinonRate W = latinonRate V := by
  have hle (X Y : LatinonMeasure) (hXY : dist X Y = 0) : latinonRate X ≤ latinonRate Y := by
    by_contra hn
    obtain ⟨y,hyY,hyX⟩ := exists_between (lt_of_not_ge hn)
    have hevent := latinon_rate_lowerSemicontinuous X y hyX
    obtain ⟨delta,hd,hsub⟩ := Metric.mem_nhds_iff.mp hevent
    have hY : Y ∈ Metric.ball X delta := by
      rw [Metric.mem_ball,dist_comm,hXY]
      exact hd
    exact (not_lt_of_ge (hsub hY).le) hyY
  exact le_antisymm (hle W V h) (hle V W (by rwa [dist_comm]))

theorem latinon_entropy_eq_of_dist_zero (W V : LatinonMeasure) (h : dist W V = 0) :
    latinonEntropy W = latinonEntropy V := by
  rw [latinonEntropy,latinonEntropy,latinon_rate_eq_of_dist_zero W V h]

/-- Sharp C4 local upper count at any threshold below the actual rate,
including singular and infinite-rate centres. -/
theorem exists_latinon_local_upper_below_rate (W : LatinonMeasure) (t : ℝ)
    (ht : ENNReal.ofReal t < latinonRate W) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n) (S : Finset (LatinArray n)),
      (∀ L ∈ S, latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t)) := by
  obtain ⟨k,hk⟩ := exists_dyadic_grid_divergence_gt W t ht
  let m := dyadicGridSize k
  have hm : 0 < m := dyadicGridSize_pos k
  let E := latinonGridTableEntropy W m
  have heta : 0 < -t-E := by dsimp only [E,m]; linarith only [hk]
  have hpos : ∀ i : Fin m, 0 < (volume : Measure I).real ((lebesgueGridPartition m hm).cell i) := by
    intro i
    change 0 < (volume : Measure I).real (lebesgueGridCell i)
    rw [lebesgueGridCell_mass hm]
    exact div_pos zero_lt_one (Nat.cast_pos.mpr hm)
  obtain ⟨delta,hd,N,hN,hcount⟩ := exists_latinon_partition_local_upper W
    (lebesgueGridPartition m hm) (lebesgueGridPartition m hm)
    (uniformSymbolPartition m hm) hpos hpos (-t-E) heta
  refine ⟨delta,hd,N,hN,?_⟩
  intro n hn S hS
  have hc := hcount n hn S hS
  rw [latinon_uniform_partition_entropy_eq_grid W hm] at hc
  have heq : Real.log (n : ℝ)-2+latinonGridTableEntropy W m+(-t-E) =
      Real.log (n : ℝ)-2-t := by dsimp only [E]; ring
  rwa [heq] at hc

theorem exists_infinite_rate_latinon_local_upper (W : LatinonMeasure)
    (h : latinonRate W = ⊤) (t : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n) (S : Finset (LatinArray n)),
      (∀ L ∈ S, latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t)) := by
  apply exists_latinon_local_upper_below_rate W t
  rw [h]
  exact ENNReal.ofReal_lt_top

end LatinonEntropy

#print axioms LatinonEntropy.latinon_rate_eq_iSup_dyadic
#print axioms LatinonEntropy.exists_dyadic_grid_divergence_gt
#print axioms LatinonEntropy.latinon_rate_lowerSemicontinuous
#print axioms LatinonEntropy.latinon_rate_eq_of_dist_zero
#print axioms LatinonEntropy.latinon_entropy_eq_of_dist_zero
#print axioms LatinonEntropy.exists_latinon_local_upper_below_rate
#print axioms LatinonEntropy.exists_infinite_rate_latinon_local_upper
