module

public import LatinBlockData

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem latin_block_fiber_product {n r s q : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (i : Fin r) (j : Fin s) (k : Fin q) :
    latinBlockFiber row col sym ((i,j),k) =
      ((univ.filter (fun x => row x = i)) ×ˢ (univ.filter (fun y => col y = j))) ×ˢ
        (univ.filter (fun z => sym z = k)) := by
  ext t
  rcases t with ⟨⟨x,y⟩,z⟩
  simp [latinBlockFiber,finiteImageFiber,latinTripleBlock,latinBlockValue]

theorem latin_block_fiber_card {n r s q : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (i : Fin r) (j : Fin s) (k : Fin q) :
    (latinBlockFiber row col sym ((i,j),k)).card =
      (univ.filter (fun x => row x = i)).card*(univ.filter (fun y => col y = j)).card*
        (univ.filter (fun z => sym z = k)).card := by
  rw [latin_block_fiber_product,card_product,card_product]

theorem latin_block_volume_product {n r s q : ℕ}
    (row : Fin n → Fin r) (col : Fin n → Fin s) (sym : Fin n → Fin q)
    (i : Fin r) (j : Fin s) (k : Fin q) :
    latinBlockVolume row col sym ((i,j),k) =
      (((univ.filter (fun x => row x = i)).card : ℝ)/(n : ℝ))*
      (((univ.filter (fun y => col y = j)).card : ℝ)/(n : ℝ))*
      (((univ.filter (fun z => sym z = k)).card : ℝ)/(n : ℝ)) := by
  simp only [latinBlockVolume,latin_block_fiber_card,Nat.cast_mul,div_eq_mul_inv]
  ring

end LatinonEntropy
