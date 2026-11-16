module

public import SymbolIntervalClasses
public import HistoryLatinArray

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_row_nat_symbol_sum_le_one {n : ℕ} (L : LatinArray n) (x : Fin n) (k : ℕ) :
    (∑ y, if (L.val x y).val = k then (1 : ℝ) else 0) ≤ 1 := by
  rw [(L.property.1 x).sum_comp (fun z : Fin n => if z.val = k then (1 : ℝ) else 0)]
  by_cases hk : k < n
  · have he : ∀ z : Fin n, (if z.val = k then (1 : ℝ) else 0) =
        (if z = (⟨k,hk⟩ : Fin n) then 1 else 0) := by
      intro z
      simp only [Fin.ext_iff]
    simp_rw [he]
    simp
  · have he : ∀ z : Fin n, z.val ≠ k := by intro z; have hz := z.isLt; omega
    simp only [he,ite_false,sum_const_zero]
    norm_num

theorem latin_boundary_symbol_sum_le {n : ℕ} (L : LatinArray n) (a : ℝ) :
    (∑ x, ∑ y, symbolBoundaryIndicator (L.val x y) a) ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _x : Fin n, (1 : ℝ) :=
      sum_le_sum (fun x _ => latin_row_nat_symbol_sum_le_one L x (symbolFloorCut n a))
    _ = _ := by simp

def latinIntervalWeightedCount {n : ℕ} (L : LatinArray n)
    (u v : Fin n → ℝ) (a b : ℝ) : ℝ :=
  ∑ x, ∑ y, u x*v y*symbolIntervalWeight (L.val x y) a b

def latinIntervalClassWeightedCount {n : ℕ} (L : LatinArray n)
    (u v : Fin n → ℝ) (a b : ℝ) : ℝ :=
  ∑ x, ∑ y, u x*v y*symbolFloorIndicator (L.val x y) a b

/-- Only the two endpoint symbols can differ, and each contributes at most n. -/
theorem latin_interval_boundary_error {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (u v : Fin n → ℝ) (hu : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |latinIntervalWeightedCount L u v a b-latinIntervalClassWeightedCount L u v a b| ≤
      2*(n : ℝ) := by
  let t : Fin n → Fin n → ℝ := fun x y =>
    u x*v y*(symbolIntervalWeight (L.val x y) a b-symbolFloorIndicator (L.val x y) a b)
  have he : latinIntervalWeightedCount L u v a b-latinIntervalClassWeightedCount L u v a b =
      ∑ x, ∑ y, t x y := by
    unfold latinIntervalWeightedCount latinIntervalClassWeightedCount
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro y _
    dsimp only [t]
    ring
  have ht : ∀ x y, |t x y| ≤
      symbolBoundaryIndicator (L.val x y) a+symbolBoundaryIndicator (L.val x y) b := by
    intro x y
    have hprod0 : 0 ≤ u x*v y := mul_nonneg (hu x).1 (hv y).1
    have hprod1 : u x*v y ≤ 1 := by
      calc u x*v y ≤ 1*1 := mul_le_mul (hu x).2 (hv y).2 (hv y).1 (by norm_num)
           _ = 1 := one_mul 1
    calc
      _ = (u x*v y)*|symbolIntervalWeight (L.val x y) a b-symbolFloorIndicator (L.val x y) a b| := by
        dsimp only [t]
        rw [abs_mul,abs_of_nonneg hprod0]
      _ ≤ 1*|symbolIntervalWeight (L.val x y) a b-symbolFloorIndicator (L.val x y) a b| :=
        mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact symbolIntervalWeight_indicator_error hn (L.val x y) a b ha hb
  rw [he]
  calc
    _ ≤ ∑ x, |∑ y, t x y| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |t x y| := sum_le_sum (fun x _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, (symbolBoundaryIndicator (L.val x y) a+symbolBoundaryIndicator (L.val x y) b) :=
      sum_le_sum (fun x _ => sum_le_sum (fun y _ => ht x y))
    _ = (∑ x, ∑ y, symbolBoundaryIndicator (L.val x y) a)+
        (∑ x, ∑ y, symbolBoundaryIndicator (L.val x y) b) := by simp only [sum_add_distrib]
    _ ≤ (n : ℝ)+(n : ℝ) := add_le_add (latin_boundary_symbol_sum_le L a) (latin_boundary_symbol_sum_le L b)
    _ = _ := by ring

theorem latin_interval_boundary_error_normalized {n : ℕ} (hn : 0 < n) (L : LatinArray n)
    (u v : Fin n → ℝ) (hu : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hv : ∀ y, 0 ≤ v y ∧ v y ≤ 1) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |latinIntervalWeightedCount L u v a b/(n : ℝ)^2-
      latinIntervalClassWeightedCount L u v a b/(n : ℝ)^2| ≤ 2/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hnR)]
  have h := div_le_div_of_nonneg_right (latin_interval_boundary_error hn L u v hu hv a b ha hb)
    (sq_nonneg (n : ℝ))
  have he : 2*(n : ℝ)/(n : ℝ)^2 = 2/(n : ℝ) := by
    field_simp [hnR.ne']
  exact h.trans_eq he

end LatinonEntropy

#print axioms LatinonEntropy.latin_row_nat_symbol_sum_le_one
#print axioms LatinonEntropy.latin_boundary_symbol_sum_le
#print axioms LatinonEntropy.latin_interval_boundary_error
#print axioms LatinonEntropy.latin_interval_boundary_error_normalized
