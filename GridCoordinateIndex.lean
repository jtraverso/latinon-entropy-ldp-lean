module

public import FiniteCellKL
public import LebesgueGridPartition
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Each coordinate is classified separately; zero goes to the first cell. -/
def unitGridIndex (n : ℕ) (hn : 0 < n) : I → Fin n :=
  finiteCellIndex lebesgueGridCell ⟨0,hn⟩

theorem unitGridIndex_measurable (n : ℕ) (hn : 0 < n) : Measurable (unitGridIndex n hn) :=
  finiteCellIndex_measurable lebesgueGridCell ⟨0,hn⟩ lebesgueGridCell_measurable
    (lebesgueGridCell_disjoint hn)

theorem unitGridIndex_of_mem {n : ℕ} (hn : 0 < n) {u : I} {i : Fin n}
    (hi : u ∈ lebesgueGridCell i) : unitGridIndex n hn u = i :=
  finiteCellIndex_of_mem lebesgueGridCell ⟨0,hn⟩ (lebesgueGridCell_disjoint hn) hi

theorem unitGridIndex_zero (n : ℕ) (hn : 0 < n) : unitGridIndex n hn 0 = ⟨0,hn⟩ := by
  have hx : ¬ ∃ i : Fin n, (0 : I) ∈ lebesgueGridCell i := by
    rintro ⟨i,hi⟩
    have hlo : 0 ≤ symbolGridLower i :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)
    change symbolGridLower i < (0 : ℝ) ∧ (0 : ℝ) ≤ symbolGridUpper i at hi
    linarith only [hlo,hi.1]
  exact dite_eq_right hx

theorem unitGridIndex_location (n : ℕ) (hn : 0 < n) (u : I) :
    symbolGridLower (unitGridIndex n hn u) ≤ (u : ℝ) ∧
      (u : ℝ) ≤ symbolGridUpper (unitGridIndex n hn u) := by
  by_cases hu : u = 0
  · subst u
    rw [unitGridIndex_zero]
    simp only [symbolGridLower,symbolGridUpper,Nat.cast_zero,zero_div,zero_add]
    exact ⟨le_rfl,div_nonneg zero_le_one (Nat.cast_nonneg n)⟩
  · have hne : (u : ℝ) ≠ 0 := fun h => hu (Subtype.ext h)
    have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 hne.symm
    obtain ⟨i,hi⟩ := lebesgueGridCell_cover_positive hn u hpos
    rw [unitGridIndex_of_mem hn hi]
    exact ⟨hi.1.le,hi.2⟩

theorem unitGridIndex_error (n : ℕ) (hn : 0 < n) (u : I) :
    |(u : ℝ)-symbolGridLower (unitGridIndex n hn u)| ≤ 1/(n : ℝ) := by
  have h := unitGridIndex_location n hn u
  have hw := symbolGrid_width (unitGridIndex n hn u)
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith only [h.2,hw]

def gridIndexParent (n : ℕ) (j : Fin (2*n)) : Fin n :=
  ⟨j.val/2,by have hj := j.isLt; omega⟩

theorem lebesgueGridCell_parent_subset (n : ℕ) (hn : 0 < n) (j : Fin (2*n)) :
    lebesgueGridCell j ⊆ lebesgueGridCell (gridIndexParent n j) := by
  let i := gridIndexParent n j
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h2nR : (0 : ℝ) < (2*n : ℕ) := Nat.cast_pos.mpr (by omega)
  have hloNat : 2*i.val ≤ j.val := by change 2*(j.val/2) ≤ j.val; omega
  have hhiNat : j.val+1 ≤ 2*(i.val+1) := by change j.val+1 ≤ 2*(j.val/2+1); omega
  have hloR : (2 : ℝ)*(i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hloNat
  have hhiR : (j.val : ℝ)+1 ≤ 2*((i.val : ℝ)+1) := by exact_mod_cast hhiNat
  have hl : symbolGridLower i ≤ symbolGridLower j := by
    unfold symbolGridLower
    apply (div_le_div_iff₀ hnR h2nR).mpr
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hp := mul_le_mul_of_nonneg_right hloR hnR.le
    nlinarith only [hp]
  have hh : symbolGridUpper j ≤ symbolGridUpper i := by
    unfold symbolGridUpper
    apply (div_le_div_iff₀ h2nR hnR).mpr
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    have hp := mul_le_mul_of_nonneg_right hhiR hnR.le
    nlinarith only [hp]
  intro u hu
  exact ⟨hl.trans_lt hu.1,hu.2.trans hh⟩

/-- Exact refinement,including the boundary point zero. -/
theorem unitGridIndex_refine (n : ℕ) (hn : 0 < n) :
    unitGridIndex n hn = gridIndexParent n ∘ unitGridIndex (2*n) (by omega) := by
  funext u
  change unitGridIndex n hn u = gridIndexParent n (unitGridIndex (2*n) (by omega) u)
  by_cases hu : u = 0
  · subst u
    rw [unitGridIndex_zero,unitGridIndex_zero]
    apply Fin.ext
    simp [gridIndexParent]
  · have hne : (u : ℝ) ≠ 0 := fun h => hu (Subtype.ext h)
    have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 hne.symm
    obtain ⟨j,hj⟩ := lebesgueGridCell_cover_positive (by omega : 0 < 2*n) u hpos
    rw [unitGridIndex_of_mem (by omega : 0 < 2*n) hj,
      unitGridIndex_of_mem hn (lebesgueGridCell_parent_subset n hn j hj)]

end LatinonEntropy

#print axioms LatinonEntropy.unitGridIndex_measurable
#print axioms LatinonEntropy.unitGridIndex_of_mem
#print axioms LatinonEntropy.unitGridIndex_zero
#print axioms LatinonEntropy.unitGridIndex_location
#print axioms LatinonEntropy.unitGridIndex_error
#print axioms LatinonEntropy.lebesgueGridCell_parent_subset
#print axioms LatinonEntropy.unitGridIndex_refine
