module

public import LatinRevealAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem latin_chosen_symbol_owners {n : ℕ} (L : LatinArray n) (xy : LatinCell n) :
    latinRowOwner L xy (latinCellValue xy L) = xy.2 ∧
      latinColOwner L xy (latinCellValue xy L) = xy.1 := by
  constructor
  · exact (Equiv.ofBijective (L.val xy.1) (L.property.1 xy.1)).symm_apply_apply xy.2
  · exact (Equiv.ofBijective (fun x => L.val x xy.2) (L.property.2 xy.2)).symm_apply_apply xy.1

theorem latin_alternative_blockers {n : ℕ} (L : LatinArray n) (xy : LatinCell n)
    (z : Fin n) (hz : z ≠ latinCellValue xy L) :
    (xy.1,latinRowOwner L xy z) ≠ xy ∧
      (latinColOwner L xy z,xy.2) ≠ xy ∧
      (xy.1,latinRowOwner L xy z) ≠ (latinColOwner L xy z,xy.2) := by
  have hr : (xy.1,latinRowOwner L xy z) ≠ xy := by
    intro he
    apply hz
    exact (latin_row_owner_value L xy z).symm.trans
      (congrArg (fun uv : LatinCell n => L.val uv.1 uv.2) he)
  have hc : (latinColOwner L xy z,xy.2) ≠ xy := by
    intro he
    apply hz
    exact (latin_col_owner_value L xy z).symm.trans
      (congrArg (fun uv : LatinCell n => L.val uv.1 uv.2) he)
  refine ⟨hr,hc,?_⟩
  intro he
  apply hc
  exact Prod.ext (congrArg Prod.fst he).symm rfl

end LatinonEntropy

#print axioms LatinonEntropy.latin_alternative_blockers
