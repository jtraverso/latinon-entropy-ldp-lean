module

public import FiniteAverages
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

noncomputable section

namespace LatinonEntropy

def finitePriorityKey {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}
    (lam : I → Fin M) (i : I) : ℕ :=
  (lam i : ℕ)*Fintype.card I+(Fintype.equivFin I i).val

theorem finitePriorityKey_injective {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}
    (lam : I → Fin M) : Function.Injective (finitePriorityKey lam) := by
  intro i j he
  have hm := congrArg (fun k => k % Fintype.card I) he
  simp only [finitePriorityKey,
    Nat.mul_add_mod_of_lt (Fintype.equivFin I i).isLt,
    Nat.mul_add_mod_of_lt (Fintype.equivFin I j).isLt] at hm
  exact (Fintype.equivFin I).injective (Fin.ext hm)

theorem label_le_of_finitePriorityKey_le {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ}
    (lam : I → Fin M) (i j : I) (he : finitePriorityKey lam i ≤ finitePriorityKey lam j) :
    lam i ≤ lam j := by
  by_contra hnot
  have hv : (lam j : ℕ)+1 ≤ lam i := Nat.succ_le_of_lt (Fin.lt_def.mp (lt_of_not_ge hnot))
  have hj := (Fintype.equivFin I j).isLt
  unfold finitePriorityKey at he
  nlinarith

end LatinonEntropy

#print axioms LatinonEntropy.finitePriorityKey_injective
#print axioms LatinonEntropy.label_le_of_finitePriorityKey_le
