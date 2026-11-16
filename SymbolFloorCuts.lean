module

public import SymbolIntervalWeights
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

def symbolFloorCut (n : ℕ) (a : ℝ) : ℕ := ⌊(n : ℝ)*a⌋₊

theorem symbolFloorCut_mono (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    symbolFloorCut n a ≤ symbolFloorCut n b :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg n))

theorem symbolFloorCut_zero (n : ℕ) : symbolFloorCut n 0 = 0 := by simp [symbolFloorCut]

theorem symbolFloorCut_one (n : ℕ) : symbolFloorCut n 1 = n := by simp [symbolFloorCut]

theorem symbolFloorCut_le_order (n : ℕ) {a : ℝ} (ha : a ≤ 1) : symbolFloorCut n a ≤ n := by
  apply Nat.floor_le_of_le
  nlinarith only [ha,Nat.cast_nonneg (α := ℝ) n]

theorem symbolFloorCut_le_mul (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (symbolFloorCut n a : ℝ) ≤ (n : ℝ)*a :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ha)

theorem symbolFloorCut_mul_lt_add_one (n : ℕ) (a : ℝ) :
    (n : ℝ)*a < (symbolFloorCut n a : ℝ)+1 := Nat.lt_floor_add_one _

theorem symbolGridUpper_le_of_lt_cut {n : ℕ} (hn : 0 < n) (z : Fin n) (a : ℝ)
    (ha : 0 ≤ a) (hz : z.val < symbolFloorCut n a) : symbolGridUpper z ≤ a := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hzR : (z.val : ℝ)+1 ≤ (symbolFloorCut n a : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hz
  have hfloor := symbolFloorCut_le_mul n ha
  unfold symbolGridUpper
  apply (div_le_iff₀ hnR).mpr
  nlinarith only [hzR,hfloor]

theorem symbolGridLower_ge_of_cut_lt {n : ℕ} (hn : 0 < n) (z : Fin n) (a : ℝ)
    (hz : symbolFloorCut n a < z.val) : a ≤ symbolGridLower z := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hzR : (symbolFloorCut n a : ℝ)+1 ≤ (z.val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hz
  have hfloor := symbolFloorCut_mul_lt_add_one n a
  unfold symbolGridLower
  apply (le_div_iff₀ hnR).mpr
  nlinarith only [hzR,hfloor]

end LatinonEntropy
