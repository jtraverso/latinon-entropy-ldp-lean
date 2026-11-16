module

public import FiniteCellKL
public import LatinonGridProfile
public import LatinonRelativeEntropy
public import LatinonPartitionLocalUpper

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval ENNReal

abbrev GridBoxIndex (n : ℕ) := (Fin n × Fin n) × Fin n

def latinonGridBox {n : ℕ} (b : GridBoxIndex n) : Set LatinonPoint :=
  (lebesgueGridCell b.1.1 ×ˢ lebesgueGridCell b.1.2) ×ˢ lebesgueGridCell b.2

theorem latinonGridBox_measurable {n : ℕ} (b : GridBoxIndex n) : MeasurableSet (latinonGridBox b) :=
  ((lebesgueGridCell_measurable b.1.1).prod (lebesgueGridCell_measurable b.1.2)).prod
    (lebesgueGridCell_measurable b.2)

theorem latinonGridBox_disjoint {n : ℕ} (hn : 0 < n) (b c : GridBoxIndex n) (hne : b ≠ c) :
    Disjoint (latinonGridBox b) (latinonGridBox c) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  have h1 : b.1.1 = c.1.1 := by
    by_contra h
    exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hn _ _ h) hp.1.1 hq.1.1
  have h2 : b.1.2 = c.1.2 := by
    by_contra h
    exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hn _ _ h) hp.1.2 hq.1.2
  have h3 : b.2 = c.2 := by
    by_contra h
    exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hn _ _ h) hp.2 hq.2
  exact hne (Prod.ext (Prod.ext h1 h2) h3)

theorem latinonGridBox_cover (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ p ∂W.measure, ∃ b : GridBoxIndex n, p ∈ latinonGridBox b := by
  have h1 := (latinon_first_coordinate_preserving W).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  have h2 := (latinon_second_coordinate_preserving W).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  have h3 := (latinon_third_coordinate_preserving W).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hn)
  filter_upwards [h1,h2,h3] with p hp hq hr
  obtain ⟨i,hi⟩ := hp
  obtain ⟨j,hj⟩ := hq
  obtain ⟨k,hk⟩ := hr
  exact ⟨((i,j),k),⟨⟨hi,hj⟩,hk⟩⟩

theorem uniform_latinon_grid_box_mass {n : ℕ} (hn : 0 < n) (b : GridBoxIndex n) :
    uniformLatinonMeasure.measure.real (latinonGridBox b) = (1/(n : ℝ))^3 := by
  change (((volume : Measure I).prod volume).prod volume).real
    ((lebesgueGridCell b.1.1 ×ˢ lebesgueGridCell b.1.2) ×ˢ lebesgueGridCell b.2) = _
  rw [measureReal_prod_prod,measureReal_prod_prod,
    lebesgueGridCell_mass hn,lebesgueGridCell_mass hn,lebesgueGridCell_mass hn]
  ring

def latinonGridTableEntropy (W : LatinonMeasure) (n : ℕ) : ℝ :=
  ∑ b : GridBoxIndex n, W.measure.real (latinonGridBox b)*
    Real.log (uniformLatinonMeasure.measure.real (latinonGridBox b)/W.measure.real (latinonGridBox b))

/-- The inequality is for the actual cell masses of any Latinon,including
singular measures. Neither table entropy nor KL finiteness is assumed. -/
theorem latinon_grid_table_divergence_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (-latinonGridTableEntropy W n) ≤ latinonRate W := by
  let z : Fin n := ⟨0,hn⟩
  have hpos : ∀ b : GridBoxIndex n, uniformLatinonMeasure.measure (latinonGridBox b) ≠ 0 := by
    intro b hz
    have hp : (0 : ℝ) < uniformLatinonMeasure.measure.real (latinonGridBox b) := by
      rw [uniform_latinon_grid_box_mass hn]
      exact pow_pos (div_pos zero_lt_one (Nat.cast_pos.mpr hn)) 3
    have he : uniformLatinonMeasure.measure.real (latinonGridBox b) = 0 :=
      congrArg ENNReal.toReal hz
    linarith only [hp,he]
  exact finite_cell_table_kl_le W.measure uniformLatinonMeasure.measure latinonGridBox ((z,z),z)
    latinonGridBox_measurable (latinonGridBox_disjoint hn)
    (latinonGridBox_cover W hn) (latinonGridBox_cover uniformLatinonMeasure hn) hpos

/-- This identifies the actual measure's finite table entropy with the
density entropy already used by C3,with exact n^-3 normalization. -/
theorem latinon_grid_table_entropy_eq_density (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    latinonGridTableEntropy W n =
      latinGridDensityEntropy (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z) := by
  let m : GridBoxIndex n → ℝ := fun b => W.measure.real (latinonGridBox b)
  let N : ℝ := (n : ℝ)^3
  have hN : N ≠ 0 := pow_ne_zero _ (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne'
  have hterm : ∀ b : GridBoxIndex n,
      m b*Real.log ((1/(n : ℝ))^3/m b) = -(m b*Real.log (N*m b)) := by
    intro b
    have he : (1/(n : ℝ))^3/m b = (N*m b)⁻¹ := by
      dsimp only [N]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he,Real.log_inv]
    ring
  have hf : ∀ x y z : Fin n, (n : ℝ)*latinonGridTensor W x y z = N*m ((x,y),z) := by
    intro x y z
    unfold latinonGridTensor
    dsimp only [N,m,latinonGridBox]
    ring
  unfold latinonGridTableEntropy
  simp_rw [uniform_latinon_grid_box_mass hn]
  change (∑ b : GridBoxIndex n, m b*Real.log ((1/(n : ℝ))^3/m b)) = _
  simp_rw [hterm]
  rw [sum_neg_distrib]
  unfold latinGridDensityEntropy
  simp_rw [hf]
  have hscale : (∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, N*m ((x,y),z)*Real.log (N*m ((x,y),z))) =
      N*(∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, m ((x,y),z)*Real.log (N*m ((x,y),z))) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro z _
    ring
  rw [hscale]
  change -(∑ b : (Fin n × Fin n) × Fin n, m b*Real.log (N*m b)) =
    -(N*(∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n, m ((x,y),z)*Real.log (N*m ((x,y),z))))/N
  rw [neg_div,mul_div_cancel_left₀ _ hN]
  simp only [Fintype.sum_prod_type]

theorem latinon_grid_density_divergence_le (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (-latinGridDensityEntropy
      (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z)) ≤ latinonRate W := by
  rw [← latinon_grid_table_entropy_eq_density W hn]
  exact latinon_grid_table_divergence_le W hn

theorem latinon_entropy_le_grid_density_entropy (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    latinonEntropy W ≤ (latinGridDensityEntropy
      (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z) : EReal) := by
  let E := latinGridDensityEntropy (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z)
  have hc : (ENNReal.ofReal (-E) : EReal) ≤ (latinonRate W : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr (latinon_grid_density_divergence_le W hn)
  have hr : ((-E : ℝ) : EReal) ≤ (ENNReal.ofReal (-E) : EReal) := by
    rw [EReal.coe_ennreal_ofReal]
    exact_mod_cast (le_max_left (-E) 0)
  have h := EReal.neg_le_neg_iff.mpr (hr.trans hc)
  simpa only [latinonEntropy,EReal.coe_neg,neg_neg] using h

def uniformSymbolPartition (n : ℕ) (hn : 0 < n) : SymbolIntervalPartition n where
  q_pos := hn
  cut := fun i => (i.val : ℝ)/(n : ℝ)
  strict := by
    intro i j hij
    apply (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).mpr
    exact_mod_cast (show i.val < j.val from hij)
  first := by simp
  last := by simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem uniformSymbolPartition_interval {n : ℕ} (hn : 0 < n) (k : Fin n) :
    unitSymbolInterval ((uniformSymbolPartition n hn).left k) ((uniformSymbolPartition n hn).right k) =
      lebesgueGridCell k := by
  simp [unitSymbolInterval,uniformSymbolPartition,SymbolIntervalPartition.left,
    SymbolIntervalPartition.right,lebesgueGridCell,symbolGridCell,symbolGridLower,symbolGridUpper]

theorem uniformSymbolPartition_width {n : ℕ} (hn : 0 < n) (k : Fin n) :
    (uniformSymbolPartition n hn).right k-(uniformSymbolPartition n hn).left k = 1/(n : ℝ) := by
  simpa [uniformSymbolPartition,SymbolIntervalPartition.left,SymbolIntervalPartition.right,
    symbolGridLower,symbolGridUpper] using symbolGrid_width k

theorem latinon_uniform_partition_entropy_eq_grid (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) :
    latinonPartitionEntropy W (lebesgueGridPartition n hn) (lebesgueGridPartition n hn)
      (uniformSymbolPartition n hn) = latinonGridTableEntropy W n := by
  unfold latinonPartitionEntropy finiteTableEntropy latinonGridTableEntropy
  apply sum_congr rfl
  intro b _
  unfold latinonPartitionVolume latinonPartitionTable
  simp only [lebesgueGridPartition,uniformSymbolPartition_interval hn,
    lebesgueGridCell_mass hn,uniformSymbolPartition_width hn,uniform_latinon_grid_box_mass hn]
  have hv : (1/(n : ℝ))*(1/(n : ℝ))*(1/(n : ℝ)) = (1/(n : ℝ))^3 := by ring
  rw [hv]
  rfl

end LatinonEntropy

#print axioms LatinonEntropy.latinonGridBox_measurable
#print axioms LatinonEntropy.latinonGridBox_disjoint
#print axioms LatinonEntropy.latinonGridBox_cover
#print axioms LatinonEntropy.uniform_latinon_grid_box_mass
#print axioms LatinonEntropy.latinon_grid_table_divergence_le
#print axioms LatinonEntropy.latinon_grid_table_entropy_eq_density
#print axioms LatinonEntropy.latinon_grid_density_divergence_le
#print axioms LatinonEntropy.latinon_entropy_le_grid_density_entropy
#print axioms LatinonEntropy.uniformSymbolPartition_interval
#print axioms LatinonEntropy.uniformSymbolPartition_width
#print axioms LatinonEntropy.latinon_uniform_partition_entropy_eq_grid
#print axioms LatinonEntropy.finite_measure_ac_of_positive_reference
#print axioms LatinonEntropy.finite_rnDeriv_eq_ratio
#print axioms LatinonEntropy.finite_measure_real_univ
#print axioms LatinonEntropy.finite_kl_ne_top
#print axioms LatinonEntropy.finite_kl_toReal_eq_sum
#print axioms LatinonEntropy.finite_kl_eq_ofReal_sum
#print axioms LatinonEntropy.finite_probability_kl_eq_neg_table
#print axioms LatinonEntropy.finiteCellIndex_of_mem
#print axioms LatinonEntropy.finiteCellIndex_eq_iff_of_covered
#print axioms LatinonEntropy.finiteCellIndex_fiber
#print axioms LatinonEntropy.finiteCellIndex_measurable
#print axioms LatinonEntropy.finiteCellIndex_map_cell
#print axioms LatinonEntropy.finite_cell_table_kl_le
