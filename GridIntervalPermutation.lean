module

public import GridCoordinateIndex
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem gridLower_nonneg {n : ℕ} (i : Fin n) : 0 ≤ symbolGridLower i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gridUpper_le_one {n : ℕ} (hn : 0 < n) (i : Fin n) : symbolGridUpper i ≤ 1 := by
  unfold symbolGridUpper
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).mpr
  have hi : i.val+1 ≤ n := i.isLt
  have hir : (i.val : ℝ)+1 ≤ n := by exact_mod_cast hi
  simpa only [one_mul] using hir

def gridIntervalShift {n : ℕ} (sigma : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  symbolGridLower (sigma i)-symbolGridLower i

theorem gridIntervalShift_mem {n : ℕ} (sigma : Equiv.Perm (Fin n)) {i : Fin n} {u : I}
    (hu : u ∈ lebesgueGridCell i) :
    (u : ℝ)+gridIntervalShift sigma i ∈ symbolGridCell (sigma i) := by
  change symbolGridLower (sigma i) < _ ∧ _ ≤ symbolGridUpper (sigma i)
  have hi := symbolGrid_width i
  have hs := symbolGrid_width (sigma i)
  dsimp only [gridIntervalShift]
  exact ⟨by linarith only [hu.1],by linarith only [hu.2,hi,hs]⟩

def gridPermutationValue {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) (u : I) : ℝ :=
  if u = 0 then 0 else (u : ℝ)+gridIntervalShift sigma (unitGridIndex n hn u)

theorem gridPermutationValue_mem {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) (u : I) :
    gridPermutationValue hn sigma u ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hz : u = 0
  · simp [gridPermutationValue,hz]
  · have hr : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
      (Ne.symm (fun h => hz (Subtype.ext h)))
    obtain ⟨i,hi⟩ := lebesgueGridCell_cover_positive hn u hr
    rw [gridPermutationValue,ite_eq_right hz,unitGridIndex_of_mem hn hi]
    have hm := gridIntervalShift_mem sigma hi
    exact ⟨(gridLower_nonneg (sigma i)).trans hm.1.le,hm.2.trans (gridUpper_le_one hn (sigma i))⟩

def gridIntervalPermutation {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) (u : I) : I :=
  ⟨gridPermutationValue hn sigma u,gridPermutationValue_mem hn sigma u⟩

theorem gridIntervalPermutation_zero {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) :
    gridIntervalPermutation hn sigma 0 = 0 := by
  apply Subtype.ext
  simp [gridIntervalPermutation,gridPermutationValue]

theorem gridIntervalPermutation_val_of_mem {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    {i : Fin n} {u : I} (hu : u ∈ lebesgueGridCell i) :
    (gridIntervalPermutation hn sigma u : ℝ) = (u : ℝ)+gridIntervalShift sigma i := by
  have hz : u ≠ 0 := by
    intro h
    have hp := hu.1
    rw [h] at hp
    exact not_lt_of_ge (gridLower_nonneg i) hp
  change gridPermutationValue hn sigma u = _
  rw [gridPermutationValue,ite_eq_right hz,unitGridIndex_of_mem hn hu]

theorem gridIntervalPermutation_cell {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    {i : Fin n} {u : I} (hu : u ∈ lebesgueGridCell i) :
    gridIntervalPermutation hn sigma u ∈ lebesgueGridCell (sigma i) := by
  change (gridIntervalPermutation hn sigma u : ℝ) ∈ symbolGridCell (sigma i)
  rw [gridIntervalPermutation_val_of_mem hn sigma hu]
  exact gridIntervalShift_mem sigma hu

theorem gridIntervalPermutation_inverse {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) (u : I) :
    gridIntervalPermutation hn sigma.symm (gridIntervalPermutation hn sigma u) = u := by
  by_cases hz : u = 0
  · subst u
    rw [gridIntervalPermutation_zero,gridIntervalPermutation_zero]
  · have hr : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
      (Ne.symm (fun h => hz (Subtype.ext h)))
    obtain ⟨i,hi⟩ := lebesgueGridCell_cover_positive hn u hr
    apply Subtype.ext
    rw [gridIntervalPermutation_val_of_mem hn sigma.symm (gridIntervalPermutation_cell hn sigma hi),
      gridIntervalPermutation_val_of_mem hn sigma hi]
    simp only [gridIntervalShift,sigma.symm_apply_apply]
    ring

theorem gridIntervalPermutation_measurable {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) :
    Measurable (gridIntervalPermutation hn sigma) := by
  have hs : Measurable (fun i : Fin n => gridIntervalShift sigma i) := measurable_of_countable _
  have ha := measurable_subtype_coe.add (hs.comp (unitGridIndex_measurable n hn))
  have hv : Measurable (gridPermutationValue hn sigma) :=
    measurable_const.ite (measurableSet_singleton (0 : I)) ha
  exact hv.subtype_mk

def gridIntervalMeasurableEquiv {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) : I ≃ᵐ I where
  toFun := gridIntervalPermutation hn sigma
  invFun := gridIntervalPermutation hn sigma.symm
  left_inv := gridIntervalPermutation_inverse hn sigma
  right_inv := gridIntervalPermutation_inverse hn sigma.symm
  measurable_toFun := gridIntervalPermutation_measurable hn sigma
  measurable_invFun := gridIntervalPermutation_measurable hn sigma.symm

end LatinonEntropy

#print axioms LatinonEntropy.gridLower_nonneg
#print axioms LatinonEntropy.gridUpper_le_one
#print axioms LatinonEntropy.gridIntervalShift_mem
#print axioms LatinonEntropy.gridPermutationValue_mem
#print axioms LatinonEntropy.gridIntervalPermutation_zero
#print axioms LatinonEntropy.gridIntervalPermutation_val_of_mem
#print axioms LatinonEntropy.gridIntervalPermutation_cell
#print axioms LatinonEntropy.gridIntervalPermutation_inverse
#print axioms LatinonEntropy.gridIntervalPermutation_measurable
#print axioms LatinonEntropy.gridIntervalMeasurableEquiv
