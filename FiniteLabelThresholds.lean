module

public import FiniteLabelPairs
public import LabelAveraging

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

theorem finiteMean_two_label_thresholds {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} (u v : V) (huv : u ≠ v) (t : Fin M) (w : ℝ) :
    finiteMean (fun lam : V → Fin M => if t ≤ lam u ∧ t ≤ lam v then w else 0) =
      (((M : ℝ)-t)/M)^2*w := by
  let : Nonempty (Fin M) := ⟨t⟩
  let f : Fin M → ℝ := fun z => if t ≤ z then 1 else 0
  have hfun : (fun lam : V → Fin M => if t ≤ lam u ∧ t ≤ lam v then w else 0) =
      (fun lam => w*(f (lam u)*f (lam v))) := by
    funext lam
    by_cases hu : t ≤ lam u <;> by_cases hv : t ≤ lam v <;> simp [f,hu,hv]
  rw [hfun,finiteMean_mul,finiteMean_distinct_coordinates u v huv f f]
  have hf : finiteMean f = ((M : ℝ)-t)/M := by
    simpa only [mul_one] using finiteMean_label_ge t (1 : ℝ)
  rw [hf]
  ring

end LatinonEntropy

#print axioms LatinonEntropy.finiteMean_two_label_thresholds
