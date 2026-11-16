module

public import HistoryLatinArray
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

def symbolRelabelEquiv {n : ℕ} (sigma : Equiv.Perm (Fin n)) : LatinArray n ≃ LatinArray n where
  toFun L := ⟨fun x y => sigma (L.val x y),
    (fun x => sigma.bijective.comp (L.property.1 x)),
    (fun y => sigma.bijective.comp (L.property.2 y))⟩
  invFun L := ⟨fun x y => sigma.symm (L.val x y),
    (fun x => sigma.symm.bijective.comp (L.property.1 x)),
    (fun y => sigma.symm.bijective.comp (L.property.2 y))⟩
  left_inv L := by
    apply Subtype.ext
    funext x y
    exact sigma.symm_apply_apply (L.val x y)
  right_inv L := by
    apply Subtype.ext
    funext x y
    exact sigma.apply_symm_apply (L.val x y)

def symbolBlockStabilizer {n q : ℕ} (color : Fin n → Fin q) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {sigma | ∀ z, color (sigma z) = color z}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro sigma tau hs ht z
    change color (sigma (tau z)) = color z
    rw [hs,ht]
  inv_mem' := by
    intro sigma hs z
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using (hs (sigma.symm z)).symm

theorem symbol_relabel_preserves_block {n q : ℕ} (color : Fin n → Fin q)
    (g : symbolBlockStabilizer color) (L : LatinArray n) (x y : Fin n) :
    color ((symbolRelabelEquiv g.val L).val x y) = color (L.val x y) := g.property _

theorem swap_mem_symbolBlockStabilizer {n q : ℕ} (color : Fin n → Fin q)
    (a b : Fin n) (hab : color a = color b) :
    Equiv.swap a b ∈ symbolBlockStabilizer color := by
  intro z
  by_cases ha : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  · by_cases hb : z = b
    · subst z
      simpa only [Equiv.swap_apply_right] using hab
    · simp only [Equiv.swap_apply_of_ne_of_ne ha hb]

end LatinonEntropy

#print axioms LatinonEntropy.symbol_relabel_preserves_block
#print axioms LatinonEntropy.swap_mem_symbolBlockStabilizer
