module

public import FiniteAverages

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

/-- The two distinct blocking cells retain independent finite labels,
also after the current cell's label has been fixed. -/
theorem finiteMean_distinct_coordinates {V B : Type*} [Fintype V] [DecidableEq V]
    [Fintype B] [Nonempty B] (i j : V) (hij : i ≠ j) (f g : B → ℝ) :
    finiteMean (fun lam : V → B => f (lam i)*g (lam j)) = finiteMean f*finiteMean g := by
  rw [finiteMean_split i]
  have hji : j ≠ i := Ne.symm hij
  have he : ∀ t : B,
      finiteMean (fun rest : {k : V // k ≠ i} → B =>
        f (((Equiv.funSplitAt i B).symm (t,rest)) i)*
          g (((Equiv.funSplitAt i B).symm (t,rest)) j)) = f t*finiteMean g := by
    intro t
    have hfun : (fun rest : {k : V // k ≠ i} → B =>
        f (((Equiv.funSplitAt i B).symm (t,rest)) i)*
          g (((Equiv.funSplitAt i B).symm (t,rest)) j)) =
        (fun rest => f t*g (rest ⟨j,hji⟩)) := by
      funext rest
      simp [Equiv.funSplitAt_symm_apply,hji]
    rw [hfun,finiteMean_mul,finiteMean_coordinate]
  simp_rw [he]
  have hcomm : (fun t => f t*finiteMean g) = (fun t => finiteMean g*f t) :=
    funext (fun _ => mul_comm _ _)
  rw [hcomm,finiteMean_mul,mul_comm]

end LatinonEntropy

#print axioms LatinonEntropy.finiteMean_distinct_coordinates
