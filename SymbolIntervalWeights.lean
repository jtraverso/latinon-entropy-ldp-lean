module

public import FiniteAverages
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical

def symbolGridLower {n : ℕ} (z : Fin n) : ℝ := (z.val : ℝ)/(n : ℝ)

def symbolGridUpper {n : ℕ} (z : Fin n) : ℝ := ((z.val : ℝ)+1)/(n : ℝ)

def symbolGridCell {n : ℕ} (z : Fin n) : Set ℝ := Set.Ioc (symbolGridLower z) (symbolGridUpper z)

/-- The actual Lebesgue fraction of a symbol cell contained in an interval. -/
def symbolIntervalWeight {n : ℕ} (z : Fin n) (a b : ℝ) : ℝ :=
  (n : ℝ)*volume.real (symbolGridCell z ∩ Set.Ioc a b)

theorem symbolGrid_width {n : ℕ} (z : Fin n) :
    symbolGridUpper z-symbolGridLower z = 1/(n : ℝ) := by
  unfold symbolGridUpper symbolGridLower
  ring

theorem symbolGrid_scaled_width {n : ℕ} (hn : 0 < n) (z : Fin n) :
    (n : ℝ)*(symbolGridUpper z-symbolGridLower z) = 1 := by
  rw [symbolGrid_width]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem symbolGrid_width_nonneg {n : ℕ} (z : Fin n) :
    0 ≤ symbolGridUpper z-symbolGridLower z := by
  rw [symbolGrid_width]
  exact div_nonneg (by norm_num) (Nat.cast_nonneg n)

theorem symbolIntervalWeight_formula {n : ℕ} (z : Fin n) (a b : ℝ) :
    symbolIntervalWeight z a b =
      (n : ℝ)*max (min (symbolGridUpper z) b-max (symbolGridLower z) a) 0 := by
  have hs : symbolGridCell z ∩ Set.Ioc a b =
      Set.Ioc (max (symbolGridLower z) a) (min (symbolGridUpper z) b) := by
    ext x
    simp only [symbolGridCell,Set.mem_inter_iff,Set.mem_Ioc,max_lt_iff,le_min_iff]
    tauto
  rw [symbolIntervalWeight,hs,Real.volume_real_Ioc]

theorem symbolIntervalWeight_nonneg {n : ℕ} (z : Fin n) (a b : ℝ) :
    0 ≤ symbolIntervalWeight z a b := by
  rw [symbolIntervalWeight_formula]
  exact mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _)

theorem symbolIntervalWeight_le_one {n : ℕ} (hn : 0 < n) (z : Fin n) (a b : ℝ) :
    symbolIntervalWeight z a b ≤ 1 := by
  have hd : min (symbolGridUpper z) b-max (symbolGridLower z) a ≤
      symbolGridUpper z-symbolGridLower z := by
    have hu := min_le_left (symbolGridUpper z) b
    have hl := le_max_left (symbolGridLower z) a
    linarith only [hu,hl]
  rw [symbolIntervalWeight_formula]
  exact (mul_le_mul_of_nonneg_left (max_le hd (symbolGrid_width_nonneg z))
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).trans_eq (symbolGrid_scaled_width hn z)

theorem symbolIntervalWeight_eq_one {n : ℕ} (hn : 0 < n) (z : Fin n) (a b : ℝ)
    (ha : a ≤ symbolGridLower z) (hb : symbolGridUpper z ≤ b) :
    symbolIntervalWeight z a b = 1 := by
  rw [symbolIntervalWeight_formula,min_eq_left hb,max_eq_left ha,
    max_eq_left (symbolGrid_width_nonneg z)]
  exact symbolGrid_scaled_width hn z

theorem symbolIntervalWeight_eq_zero_left {n : ℕ} (z : Fin n) (a b : ℝ)
    (ha : symbolGridUpper z ≤ a) : symbolIntervalWeight z a b = 0 := by
  have hd : min (symbolGridUpper z) b-max (symbolGridLower z) a ≤ 0 := by
    have hu := min_le_left (symbolGridUpper z) b
    have hl := le_max_right (symbolGridLower z) a
    linarith only [hu,hl,ha]
  rw [symbolIntervalWeight_formula,max_eq_right hd,mul_zero]

theorem symbolIntervalWeight_eq_zero_right {n : ℕ} (z : Fin n) (a b : ℝ)
    (hb : b ≤ symbolGridLower z) : symbolIntervalWeight z a b = 0 := by
  have hd : min (symbolGridUpper z) b-max (symbolGridLower z) a ≤ 0 := by
    have hu := min_le_right (symbolGridUpper z) b
    have hl := le_max_left (symbolGridLower z) a
    linarith only [hu,hl,hb]
  rw [symbolIntervalWeight_formula,max_eq_right hd,mul_zero]

end LatinonEntropy
