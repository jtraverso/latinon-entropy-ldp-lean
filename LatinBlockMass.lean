module

public import LatinBlockData

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latinBlockFiber_nonempty {n r s q : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) (hb : b ∈ latinActiveBlocks row col sym) :
    (latinBlockFiber row col sym b).Nonempty := by
  obtain ⟨t,_,ht⟩ := mem_image.mp hb
  refine ⟨t,?_⟩
  simp only [latinBlockFiber,finiteImageFiber,mem_filter,mem_univ,true_and]
  exact ht

theorem latin_law_block_mass_nonneg {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 ≤ w L)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    0 ≤ latinLawBlockMass S w row col sym b := by
  rw [latin_law_block_mass_eq_fiber_sum]
  exact sum_nonneg (fun t _ => latinFamilyMarginal_nonneg S w hw t.1 t.2)

theorem latin_law_block_mass_total {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) (htotal : ∑ L ∈ S, w L = 1)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    (∑ b ∈ latinActiveBlocks row col sym, latinLawBlockMass S w row col sym b) = (n : ℝ)^2 := by
  have hs := sum_by_coordinate (univ : Finset (LatinTriple n)) (latinTripleBlock row col sym)
    (fun (_ : LatinBlock r s q) t => latinTripleWeight S w t)
  change (∑ t : LatinTriple n, latinTripleWeight S w t) =
    ∑ b ∈ latinActiveBlocks row col sym, ∑ t ∈ latinBlockFiber row col sym b, latinTripleWeight S w t at hs
  simp_rw [← latin_law_block_mass_eq_fiber_sum] at hs
  exact hs.symm.trans (latin_triple_weight_total S w htotal)

theorem latin_law_block_table_nonneg {n r s q : ℕ}
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) (hw : ∀ L ∈ S, 0 ≤ w L)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) (b : LatinBlock r s q) :
    0 ≤ latinLawBlockTable S w row col sym b :=
  div_nonneg (latin_law_block_mass_nonneg S w hw row col sym b) (sq_nonneg _)

theorem latin_law_block_table_total {n r s q : ℕ} (hn : 0 < n)
    (S : Finset (LatinArray n)) (w : LatinArray n → ℝ) (htotal : ∑ L ∈ S, w L = 1)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    (∑ b ∈ latinActiveBlocks row col sym, latinLawBlockTable S w row col sym b) = 1 := by
  simp only [latinLawBlockTable]
  rw [← sum_div,latin_law_block_mass_total S w htotal]
  exact div_self (pow_ne_zero 2 (Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne')

theorem latinBlockVolume_pos {n r s q : ℕ} (hn : 0 < n)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (b : LatinBlock r s q) (hb : b ∈ latinActiveBlocks row col sym) :
    0 < latinBlockVolume row col sym b :=
  div_pos (Nat.cast_pos.mpr (card_pos.mpr (latinBlockFiber_nonempty row col sym b hb)))
    (pow_pos (Nat.cast_pos.mpr hn) 3)

theorem latin_triple_card (n : ℕ) : ((univ : Finset (LatinTriple n)).card : ℝ) = (n : ℝ)^3 := by
  change ((univ : Finset ((Fin n × Fin n) × Fin n)).card : ℝ) = (n : ℝ)^3
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  ring

theorem latin_block_volume_total {n r s q : ℕ} (hn : 0 < n)
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q) :
    (∑ b ∈ latinActiveBlocks row col sym, latinBlockVolume row col sym b) = 1 := by
  have he : ∀ b, latinBlockVolume row col sym b =
      uniformImageWeight (univ : Finset (LatinTriple n)) (latinTripleBlock row col sym) b := by
    intro b
    unfold latinBlockVolume uniformImageWeight
    rw [latin_triple_card]
    rfl
  simp_rw [he]
  let z : Fin n := ⟨0,hn⟩
  exact uniformImageWeight_total _ ⟨((z,z),z),mem_univ _⟩ _

theorem symbol_mixture_coarse_entropy_preserved {n r s q : ℕ}
    (S : Finset (LatinArray n)) (row : Fin n → Fin r) (col : Fin n → Fin s)
    (sym : Fin n → Fin q) :
    latinLawCoarseEntropy (symbolMixtureFamily sym S) (symbolMixtureWeight sym S) row col sym =
      latinLawCoarseEntropy S (fun _ => 1/(S.card : ℝ)) row col sym := by
  unfold latinLawCoarseEntropy latinLawBlockTable
  simp_rw [symbol_mixture_block_mass_preserved]

end LatinonEntropy
