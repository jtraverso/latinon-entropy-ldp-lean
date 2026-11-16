module

public import GridTensorMeasure

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

theorem latinon_first_coordinate_preserving (W : LatinonMeasure) :
    MeasurePreserving (fun p : LatinonPoint => p.1.1) W.measure volume := by
  refine ⟨measurable_fst.comp measurable_fst,?_⟩
  apply Measure.ext
  intro S hS
  have hproj : Measurable (fun p : LatinonPoint => p.1.1) := measurable_fst.comp measurable_fst
  rw [Measure.map_apply hproj hS]
  have he : (fun p : LatinonPoint => p.1.1) ⁻¹' S = (S ×ˢ Set.univ) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  rw [he,W.xy_uniform S Set.univ hS MeasurableSet.univ,measure_univ,mul_one]

theorem latinon_second_coordinate_preserving (W : LatinonMeasure) :
    MeasurePreserving (fun p : LatinonPoint => p.1.2) W.measure volume := by
  refine ⟨measurable_snd.comp measurable_fst,?_⟩
  apply Measure.ext
  intro T hT
  have hproj : Measurable (fun p : LatinonPoint => p.1.2) := measurable_snd.comp measurable_fst
  rw [Measure.map_apply hproj hT]
  have he : (fun p : LatinonPoint => p.1.2) ⁻¹' T = (Set.univ ×ˢ T) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and,and_true]
  rw [he,W.xy_uniform Set.univ T MeasurableSet.univ hT,measure_univ,one_mul]

theorem latinon_third_coordinate_preserving (W : LatinonMeasure) :
    MeasurePreserving (fun p : LatinonPoint => p.2) W.measure volume := by
  refine ⟨measurable_snd,?_⟩
  apply Measure.ext
  intro U hU
  rw [Measure.map_apply measurable_snd hU]
  have he : (fun p : LatinonPoint => p.2) ⁻¹' U = (Set.univ ×ˢ Set.univ) ×ˢ U := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]
  rw [he,W.xz_uniform Set.univ U MeasurableSet.univ hU,measure_univ,one_mul]

def latinonCoordinateGridPartition (W : LatinonMeasure) (coordinate : LatinonPoint → I)
    (hcoordinate : MeasurePreserving coordinate W.measure volume) (n : ℕ) (hn : 0 < n) :
    MeasurableFinitePartition W.measure n where
  cell := fun z => coordinate ⁻¹' lebesgueGridCell z
  measurable := fun z => (lebesgueGridCell_measurable z).preimage hcoordinate.measurable
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hn i j hij) hpi hpj
  cover := hcoordinate.quasiMeasurePreserving.ae (lebesgueGridCell_cover_ae hn)

theorem latinon_grid_sum_third (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∑ z : Fin n, W.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell z)) = volume.real S*volume.real T := by
  let G := latinonCoordinateGridPartition W (fun p => p.2) (latinon_third_coordinate_preserving W) n hn
  have he : ∀ z : Fin n, (((S ×ˢ T) ×ˢ Set.univ) ∩ G.cell z) =
      (S ×ˢ T) ×ˢ lebesgueGridCell z := by
    intro z
    ext p
    simp only [Set.mem_inter_iff,Set.mem_prod,Set.mem_univ,and_true]
    rfl
  have h := G.sum_real_inter_left ((S ×ˢ T) ×ˢ Set.univ)
    ((hS.prod hT).prod MeasurableSet.univ)
  simp_rw [he] at h
  exact h.trans (W.xy_uniform_real S T hS hT)

theorem latinon_grid_sum_second (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (S U : Set I) (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (∑ y : Fin n, W.measure.real ((S ×ˢ lebesgueGridCell y) ×ˢ U)) = volume.real S*volume.real U := by
  let G := latinonCoordinateGridPartition W (fun p => p.1.2) (latinon_second_coordinate_preserving W) n hn
  have he : ∀ y : Fin n, (((S ×ˢ Set.univ) ×ˢ U) ∩ G.cell y) =
      (S ×ˢ lebesgueGridCell y) ×ˢ U := by
    intro y
    ext p
    change ((p.1.1 ∈ S ∧ p.1.2 ∈ Set.univ) ∧ p.2 ∈ U) ∧ p.1.2 ∈ lebesgueGridCell y ↔
      (p.1.1 ∈ S ∧ p.1.2 ∈ lebesgueGridCell y) ∧ p.2 ∈ U
    simp only [Set.mem_univ,and_true]
    constructor
    · rintro ⟨⟨hs,hu⟩,hg⟩
      exact ⟨⟨hs,hg⟩,hu⟩
    · rintro ⟨⟨hs,hg⟩,hu⟩
      exact ⟨⟨hs,hu⟩,hg⟩
  have h := G.sum_real_inter_left ((S ×ˢ Set.univ) ×ˢ U)
    ((hS.prod MeasurableSet.univ).prod hU)
  simp_rw [he] at h
  exact h.trans (W.xz_uniform_real S U hS hU)

theorem latinon_grid_sum_first (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (T U : Set I) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (∑ x : Fin n, W.measure.real ((lebesgueGridCell x ×ˢ T) ×ˢ U)) = volume.real T*volume.real U := by
  let G := latinonCoordinateGridPartition W (fun p => p.1.1) (latinon_first_coordinate_preserving W) n hn
  have he : ∀ x : Fin n, (((Set.univ ×ˢ T) ×ˢ U) ∩ G.cell x) =
      (lebesgueGridCell x ×ˢ T) ×ˢ U := by
    intro x
    ext p
    change ((p.1.1 ∈ Set.univ ∧ p.1.2 ∈ T) ∧ p.2 ∈ U) ∧ p.1.1 ∈ lebesgueGridCell x ↔
      (p.1.1 ∈ lebesgueGridCell x ∧ p.1.2 ∈ T) ∧ p.2 ∈ U
    simp only [Set.mem_univ,true_and]
    constructor
    · rintro ⟨⟨ht,hu⟩,hg⟩
      exact ⟨⟨hg,ht⟩,hu⟩
    · rintro ⟨⟨hg,ht⟩,hu⟩
      exact ⟨⟨ht,hu⟩,hg⟩
  have h := G.sum_real_inter_left ((Set.univ ×ˢ T) ×ˢ U)
    ((MeasurableSet.univ.prod hT).prod hU)
  simp_rw [he] at h
  exact h.trans (W.yz_uniform_real T U hT hU)

/-- Cell averages of the actual measure, with all margins derived. -/
def latinonGridTensor (W : LatinonMeasure) {n : ℕ} (x y z : Fin n) : ℝ :=
  (n : ℝ)^2*W.measure.real ((lebesgueGridCell x ×ˢ lebesgueGridCell y) ×ˢ lebesgueGridCell z)

theorem latinon_grid_tensor_nonneg (W : LatinonMeasure) {n : ℕ} (x y z : Fin n) :
    0 ≤ latinonGridTensor W x y z := mul_nonneg (sq_nonneg _) measureReal_nonneg

theorem latinon_grid_tensor_row_mass (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) (x y : Fin n) :
    (∑ z, latinonGridTensor W x y z) = 1 := by
  simp only [latinonGridTensor,← mul_sum]
  rw [latinon_grid_sum_third W hn _ _ (lebesgueGridCell_measurable x) (lebesgueGridCell_measurable y),
    lebesgueGridCell_mass hn,lebesgueGridCell_mass hn]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem latinon_grid_tensor_col_mass (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) (x z : Fin n) :
    (∑ y, latinonGridTensor W x y z) = 1 := by
  simp only [latinonGridTensor,← mul_sum]
  rw [latinon_grid_sum_second W hn _ _ (lebesgueGridCell_measurable x) (lebesgueGridCell_measurable z),
    lebesgueGridCell_mass hn,lebesgueGridCell_mass hn]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem latinon_grid_tensor_time_mass (W : LatinonMeasure) {n : ℕ} (hn : 0 < n) (y z : Fin n) :
    (∑ x, latinonGridTensor W x y z) = 1 := by
  simp only [latinonGridTensor,← mul_sum]
  rw [latinon_grid_sum_first W hn _ _ (lebesgueGridCell_measurable y) (lebesgueGridCell_measurable z),
    lebesgueGridCell_mass hn,lebesgueGridCell_mass hn]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

end LatinonEntropy

#print axioms LatinonEntropy.latinon_first_coordinate_preserving
#print axioms LatinonEntropy.latinon_second_coordinate_preserving
#print axioms LatinonEntropy.latinon_third_coordinate_preserving
#print axioms LatinonEntropy.latinon_grid_sum_third
#print axioms LatinonEntropy.latinon_grid_sum_second
#print axioms LatinonEntropy.latinon_grid_sum_first
#print axioms LatinonEntropy.latinon_grid_tensor_nonneg
#print axioms LatinonEntropy.latinon_grid_tensor_row_mass
#print axioms LatinonEntropy.latinon_grid_tensor_col_mass
#print axioms LatinonEntropy.latinon_grid_tensor_time_mass
