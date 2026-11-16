module

public import FractionalTensorCuts
public import GridTensorMeasure
public import LatinonPseudometric

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

def gridSetWeight {n : ℕ} (S : Set I) (x : Fin n) : ℝ :=
  (n : ℝ)*volume.real (S ∩ lebesgueGridCell x)

theorem gridSetWeight_bounds {n : ℕ} (hn : 0 < n) (S : Set I) (x : Fin n) :
    0 ≤ gridSetWeight S x ∧ gridSetWeight S x ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · exact mul_nonneg hnR.le measureReal_nonneg
  · have hmass : volume.real (S ∩ lebesgueGridCell x) ≤ 1/(n : ℝ) :=
      (measureReal_mono Set.inter_subset_right).trans_eq (lebesgueGridCell_mass hn x)
    exact (mul_le_mul_of_nonneg_left hmass hnR.le).trans_eq
      (mul_div_cancel₀ 1 hnR.ne')

theorem gridTensorMeasure_weighted_box {n : ℕ}
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z) (S T U : Set I) :
    (∑ x, ∑ y, ∑ z, gridSetWeight S x*gridSetWeight T y*gridSetWeight U z*p x y z) =
      (n : ℝ)^2*(gridTensorMeasure p).real ((S ×ˢ T) ×ˢ U) := by
  rw [gridTensorMeasure_real_box p hp]
  simp only [gridSetWeight,mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

theorem finiteLatinMeasure_weighted_box {n : ℕ} (L : LatinArray n) (S T U : Set I) :
    (∑ x, ∑ y, ∑ z, gridSetWeight S x*gridSetWeight T y*gridSetWeight U z*
      (if L.val x y = z then (1 : ℝ) else 0)) =
      (n : ℝ)^2*(finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ U) := by
  have hz : ∀ x y, (∑ z, gridSetWeight S x*gridSetWeight T y*gridSetWeight U z*
      (if L.val x y = z then (1 : ℝ) else 0)) =
      gridSetWeight S x*gridSetWeight T y*gridSetWeight U (L.val x y) := by
    intro x y
    simp [mul_ite]
  simp_rw [hz]
  rw [finiteLatinMeasure_real_box]
  simp only [gridSetWeight,mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

/-- Every measurable box is a fractional tensor cut, with no boundary loss. -/
theorem tensor_cut_implies_measurable_box_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (rho : ℝ) (L : LatinArray n) (hL : L ∈ latinTensorCutFamily p rho) (S T U : Set I) :
    |(finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ U)-
      (gridTensorMeasure p).real ((S ×ˢ T) ×ˢ U)| ≤ rho := by
  have hcut := (mem_filter.mp hL).2
  have h := fractional_tensor_cut_abs_le
    (fun x y z => (if L.val x y = z then (1 : ℝ) else 0)-p x y z)
    (gridSetWeight S) (gridSetWeight T) (gridSetWeight U) (rho*(n : ℝ)^2)
    (gridSetWeight_bounds hn S) (gridSetWeight_bounds hn T) (gridSetWeight_bounds hn U) hcut
  have he : (∑ x, ∑ y, ∑ z, gridSetWeight S x*gridSetWeight T y*gridSetWeight U z*
      ((if L.val x y = z then (1 : ℝ) else 0)-p x y z)) =
      (n : ℝ)^2*((finiteLatinMeasure L).real ((S ×ˢ T) ×ˢ U)-
        (gridTensorMeasure p).real ((S ×ˢ T) ×ˢ U)) := by
    simp only [mul_sub,sum_sub_distrib]
    rw [finiteLatinMeasure_weighted_box,gridTensorMeasure_weighted_box p hp]
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg _)] at h
  have hn2 : (0 : ℝ) < (n : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  nlinarith only [h,hn2]

theorem tensor_cut_implies_latinon_distance_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → Fin n → Fin n → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hrow : ∀ x y, ∑ z, p x y z = 1)
    (hcol : ∀ x z, ∑ y, p x y z = 1)
    (htime : ∀ y z, ∑ x, p x y z = 1)
    (rho : ℝ) (L : LatinArray n) (hL : L ∈ latinTensorCutFamily p rho) :
    dist (latinArrayToLatinonMeasure hn L)
      (gridTensorToLatinonMeasure hn p hp hrow hcol htime) ≤ rho := by
  let W := latinArrayToLatinonMeasure hn L
  let V := gridTensorToLatinonMeasure hn p hp hrow hcol htime
  have hmeasure : measureCut W.measure V.measure ≤ rho := by
    apply cutValueSup_le
    intro B
    exact tensor_cut_implies_measurable_box_bound hn p hp rho L hL B.rows B.cols B.symbols
  calc
    dist W V = latinonCutDistance W V := rfl
    _ ≤ latinonAlignmentCost W V LatinonRelabel.refl LatinonRelabel.refl :=
      latinonCutDistance_le_cost W V _ _
    _ = measureCut W.measure V.measure := by
      change orderCut id id+orderCut id id+
        measureCut W.measure (relabelLatinonMeasure V.measure LatinonRelabel.refl LatinonRelabel.refl) = _
      rw [orderCut_self,relabelLatinonMeasure_refl]
      ring
    _ ≤ rho := hmeasure

end LatinonEntropy

#print axioms LatinonEntropy.gridSetWeight_bounds
#print axioms LatinonEntropy.gridTensorMeasure_weighted_box
#print axioms LatinonEntropy.finiteLatinMeasure_weighted_box
#print axioms LatinonEntropy.tensor_cut_implies_measurable_box_bound
#print axioms LatinonEntropy.tensor_cut_implies_latinon_distance_bound
