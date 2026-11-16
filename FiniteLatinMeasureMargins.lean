module

public import FiniteLatinMeasure
public import LatinonMeasureSpace

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

theorem lebesgueGrid_inter_sum {n : ℕ} (hn : 0 < n) (S : Set I) (hS : MeasurableSet S) :
    (∑ x : Fin n, volume.real (S ∩ lebesgueGridCell x)) = volume.real S :=
  (lebesgueGridPartition n hn).sum_real_inter_left S hS

theorem finiteLatinMeasure_xy_real {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ Set.univ) = volume.real S*volume.real T := by
  rw [finiteLatinMeasure_real_box]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  let a : Fin n → ℝ := fun x => volume.real (S ∩ lebesgueGridCell x)
  let b : Fin n → ℝ := fun y => volume.real (T ∩ lebesgueGridCell y)
  change (n : ℝ)*(∑ x, ∑ y, a x*b y*(1/(n : ℝ))) = _
  calc
    _ = (n : ℝ)*((∑ x, ∑ y, a x*b y)/(n : ℝ)) := by
      simp only [div_eq_mul_inv,one_mul,sum_mul]
    _ = ∑ x, ∑ y, a x*b y := mul_div_cancel₀ _ (Nat.cast_pos.mpr hn).ne'
    _ = (∑ x, a x)*(∑ y, b y) := by rw [sum_mul_sum]
    _ = _ := by
      dsimp only [a,b]
      rw [lebesgueGrid_inter_sum hn S hS,lebesgueGrid_inter_sum hn T hT]

theorem finiteLatinMeasure_xz_real {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S U : Set I)
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (finiteLatinMeasure L).real ((S ×ˢ Set.univ) ×ˢ U) = volume.real S*volume.real U := by
  rw [finiteLatinMeasure_real_box]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  let a : Fin n → ℝ := fun x => volume.real (S ∩ lebesgueGridCell x)
  let c : Fin n → ℝ := fun z => volume.real (U ∩ lebesgueGridCell z)
  change (n : ℝ)*(∑ x, ∑ y, a x*(1/(n : ℝ))*c (L.val x y)) = _
  have hr : ∀ x, (∑ y, a x*(1/(n : ℝ))*c (L.val x y)) =
      a x*(1/(n : ℝ))*(∑ z, c z) := by
    intro x
    rw [← mul_sum,(L.property.1 x).sum_comp c]
  calc
    _ = (n : ℝ)*(∑ x, a x*(1/(n : ℝ))*(∑ z, c z)) := by simp_rw [hr]
    _ = (n : ℝ)*(((∑ x, a x)*(∑ z, c z))/(n : ℝ)) := by
      rw [← sum_mul,← sum_mul]
      ring
    _ = (∑ x, a x)*(∑ z, c z) := mul_div_cancel₀ _ (Nat.cast_pos.mpr hn).ne'
    _ = _ := by
      dsimp only [a,c]
      rw [lebesgueGrid_inter_sum hn S hS,lebesgueGrid_inter_sum hn U hU]

theorem finiteLatinMeasure_yz_real {n : ℕ} (hn : 0 < n) (L : LatinArray n) (T U : Set I)
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (finiteLatinMeasure L).real ((Set.univ ×ˢ T) ×ˢ U) = volume.real T*volume.real U := by
  rw [finiteLatinMeasure_real_box]
  simp only [Set.univ_inter,lebesgueGridCell_mass hn]
  rw [sum_comm]
  let b : Fin n → ℝ := fun y => volume.real (T ∩ lebesgueGridCell y)
  let c : Fin n → ℝ := fun z => volume.real (U ∩ lebesgueGridCell z)
  change (n : ℝ)*(∑ y, ∑ x, (1/(n : ℝ))*b y*c (L.val x y)) = _
  have hc : ∀ y, (∑ x, (1/(n : ℝ))*b y*c (L.val x y)) =
      b y*(1/(n : ℝ))*(∑ z, c z) := by
    intro y
    rw [← mul_sum,(L.property.2 y).sum_comp c]
    ring
  calc
    _ = (n : ℝ)*(∑ y, b y*(1/(n : ℝ))*(∑ z, c z)) := by simp_rw [hc]
    _ = (n : ℝ)*(((∑ y, b y)*(∑ z, c z))/(n : ℝ)) := by
      rw [← sum_mul,← sum_mul]
      ring
    _ = (∑ y, b y)*(∑ z, c z) := mul_div_cancel₀ _ (Nat.cast_pos.mpr hn).ne'
    _ = _ := by
      dsimp only [b,c]
      rw [lebesgueGrid_inter_sum hn T hT,lebesgueGrid_inter_sum hn U hU]

theorem finiteLatinMeasure_xy {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    finiteLatinMeasure L ((S ×ˢ T) ×ˢ Set.univ) = volume S*volume T := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simpa only [measureReal_def,ENNReal.toReal_mul] using finiteLatinMeasure_xy_real hn L S T hS hT

theorem finiteLatinMeasure_xz {n : ℕ} (hn : 0 < n) (L : LatinArray n) (S U : Set I)
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    finiteLatinMeasure L ((S ×ˢ Set.univ) ×ˢ U) = volume S*volume U := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simpa only [measureReal_def,ENNReal.toReal_mul] using finiteLatinMeasure_xz_real hn L S U hS hU

theorem finiteLatinMeasure_yz {n : ℕ} (hn : 0 < n) (L : LatinArray n) (T U : Set I)
    (hT : MeasurableSet T) (hU : MeasurableSet U) :
    finiteLatinMeasure L ((Set.univ ×ˢ T) ×ˢ U) = volume T*volume U := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simpa only [measureReal_def,ENNReal.toReal_mul] using finiteLatinMeasure_yz_real hn L T U hT hU

/-- The square is now an actual Latinon, with the identity order map. -/
def latinArrayToLatinonMeasure {n : ℕ} (hn : 0 < n) (L : LatinArray n) : LatinonMeasure where
  measure := finiteLatinMeasure L
  order := id
  order_preserving := MeasurePreserving.id volume
  xy_uniform := finiteLatinMeasure_xy hn L
  xz_uniform := finiteLatinMeasure_xz hn L
  yz_uniform := finiteLatinMeasure_yz hn L

theorem finiteLatinMeasure_probability {n : ℕ} (hn : 0 < n) (L : LatinArray n) :
    IsProbabilityMeasure (finiteLatinMeasure L) :=
  inferInstanceAs (IsProbabilityMeasure (latinArrayToLatinonMeasure hn L).measure)

example : ∃ L : LatinArray 1, (latinArrayToLatinonMeasure (by decide) L).measure Set.univ = 1 := by
  let L : LatinArray 1 := ⟨fun _ y => y,by
    constructor
    · intro x
      exact Function.bijective_id
    · intro y
      constructor
      · intro x z _
        exact Subsingleton.elim _ _
      · intro z
        exact ⟨0,Subsingleton.elim _ _⟩⟩
  exact ⟨L,measure_univ⟩

end LatinonEntropy

#print axioms LatinonEntropy.lebesgueGrid_inter_sum
#print axioms LatinonEntropy.finiteLatinMeasure_xy_real
#print axioms LatinonEntropy.finiteLatinMeasure_xz_real
#print axioms LatinonEntropy.finiteLatinMeasure_yz_real
#print axioms LatinonEntropy.finiteLatinMeasure_xy
#print axioms LatinonEntropy.finiteLatinMeasure_xz
#print axioms LatinonEntropy.finiteLatinMeasure_yz
#print axioms LatinonEntropy.latinArrayToLatinonMeasure
#print axioms LatinonEntropy.finiteLatinMeasure_probability
