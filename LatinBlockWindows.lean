module

public import LatinBlockCounting
public import LatinBlockGeometry

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_block_mass_of_not_active {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) (hb : b ∉ latinActiveBlocks row col sym) :
    latinLawBlockMass S w row col sym b = 0 := by
  have hf : latinBlockFiber row col sym b = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    simp only [latinBlockFiber,finiteImageFiber,mem_filter,mem_univ,true_and] at ht
    exact hb (mem_image.mpr ⟨t,mem_univ _,ht⟩)
  rw [latin_law_block_mass_eq_fiber_sum,hf,sum_empty]

theorem latin_coarse_entropy_eq_full_sum {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    latinLawCoarseEntropy S w row col sym = ∑ b : LatinBlock r s q,
      latinLawBlockTable S w row col sym b*
        Real.log (latinBlockVolume row col sym b/latinLawBlockTable S w row col sym b) := by
  unfold latinLawCoarseEntropy
  apply sum_subset (subset_univ _)
  intro b _ hb
  simp only [latinLawBlockTable,latin_block_mass_of_not_active S w row col sym b hb,zero_div,zero_mul]

theorem latin_uniform_block_table_as_mean {n r s q : ℕ}
    (S : Finset (LatinArray n)) (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    latinLawBlockTable S (fun _ => 1/(S.card : ℝ)) row col sym b =
      (∑ L ∈ S, latinBlockObservable row col sym b L/(n : ℝ)^2)/(S.card : ℝ) := by
  rw [latinLawBlockTable,latin_law_block_mass_as_observable,← mul_sum]
  calc
    _ = ((∑ L ∈ S, latinBlockObservable row col sym b L)/(n : ℝ)^2)/(S.card : ℝ) := by ring
    _ = _ := by rw [sum_div]

/-- Coordinate windows are convex: the actual uniform family's mean table
inherits every common block constraint satisfied by its individual squares. -/
theorem latin_mean_block_window {n r s q : ℕ}
    (S : Finset (LatinArray n)) (hS : S.Nonempty)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (target : LatinBlock r s q → ℝ) (delta : ℝ)
    (hwindow : ∀ L ∈ S, ∀ b,
      |latinBlockObservable row col sym b L/(n : ℝ)^2-target b| ≤ delta) :
    ∀ b, |latinLawBlockTable S (fun _ => 1/(S.card : ℝ)) row col sym b-target b| ≤ delta := by
  intro b
  have hp : (0 : ℝ) < S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  rw [latin_uniform_block_table_as_mean]
  have he : (∑ L ∈ S, latinBlockObservable row col sym b L/(n : ℝ)^2)/(S.card : ℝ)-target b =
      (∑ L ∈ S, (latinBlockObservable row col sym b L/(n : ℝ)^2-target b))/(S.card : ℝ) := by
    apply (eq_div_iff hp.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hp.ne']
    simp only [sum_sub_distrib,sum_const,nsmul_eq_mul]
    ring
  rw [he,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ L ∈ S, |latinBlockObservable row col sym b L/(n : ℝ)^2-target b| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _L ∈ S, delta := sum_le_sum (fun L hL => hwindow L hL b)
    _ = _ := by simp; ring

end LatinonEntropy
