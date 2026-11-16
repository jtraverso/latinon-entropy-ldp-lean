module

public import HistoryLatinArray
public import WeightedChain

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

abbrev LatinCell (n : ℕ) := Fin n × Fin n

def latinCellValue {n : ℕ} (xy : LatinCell n) (L : LatinArray n) : Fin n := L.val xy.1 xy.2

def latinRowOwner {n : ℕ} (L : LatinArray n) (xy : LatinCell n) (z : Fin n) : Fin n :=
  (Equiv.ofBijective (L.val xy.1) (L.property.1 xy.1)).symm z

def latinColOwner {n : ℕ} (L : LatinArray n) (xy : LatinCell n) (z : Fin n) : Fin n :=
  (Equiv.ofBijective (fun x => L.val x xy.2) (L.property.2 xy.2)).symm z

theorem latin_row_owner_value {n : ℕ} (L : LatinArray n) (xy : LatinCell n) (z : Fin n) :
    L.val xy.1 (latinRowOwner L xy z) = z :=
  (Equiv.ofBijective (L.val xy.1) (L.property.1 xy.1)).apply_symm_apply z

theorem latin_col_owner_value {n : ℕ} (L : LatinArray n) (xy : LatinCell n) (z : Fin n) :
    L.val (latinColOwner L xy z) xy.2 = z :=
  (Equiv.ofBijective (fun x => L.val x xy.2) (L.property.2 xy.2)).apply_symm_apply z

theorem latin_reveal_symbol_orders {n : ℕ} (S : Finset (LatinArray n))
    (key : LatinCell n → ℕ) (L : LatinArray n) (xy : LatinCell n) (z : Fin n)
    (hz : z ∈ (revealFibre S univ key latinCellValue xy L).image (latinCellValue xy)) :
    key xy ≤ key (xy.1,latinRowOwner L xy z) ∧
      key xy ≤ key (latinColOwner L xy z,xy.2) := by
  obtain ⟨L',hL',he⟩ := mem_image.mp hz
  simp only [revealFibre,mem_filter] at hL'
  have hf := hL'.2
  constructor
  · by_contra hnot
    have hb : key (xy.1,latinRowOwner L xy z) < key xy := lt_of_not_ge hnot
    have ha := hf (xy.1,latinRowOwner L xy z) (mem_univ _) hb
    change L'.val xy.1 (latinRowOwner L xy z) = L.val xy.1 (latinRowOwner L xy z) at ha
    rw [latin_row_owner_value] at ha
    have heq : latinRowOwner L xy z = xy.2 :=
      (L'.property.1 xy.1).1 (ha.trans he.symm)
    have hp : (xy.1,latinRowOwner L xy z) = xy := Prod.ext rfl heq
    rw [hp] at hb
    exact lt_irrefl _ hb
  · by_contra hnot
    have hb : key (latinColOwner L xy z,xy.2) < key xy := lt_of_not_ge hnot
    have ha := hf (latinColOwner L xy z,xy.2) (mem_univ _) hb
    change L'.val (latinColOwner L xy z) xy.2 = L.val (latinColOwner L xy z) xy.2 at ha
    rw [latin_col_owner_value] at ha
    have heq : latinColOwner L xy z = xy.1 :=
      (L'.property.2 xy.2).1 (ha.trans he.symm)
    have hp : (latinColOwner L xy z,xy.2) = xy := Prod.ext heq rfl
    rw [hp] at hb
    exact lt_irrefl _ hb

end LatinonEntropy

#print axioms LatinonEntropy.latin_reveal_symbol_orders
