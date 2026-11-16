module

public import WeightedLogSum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def finiteMean {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (∑ i, f i) / Fintype.card I

theorem finiteMean_const {I : Type*} [Fintype I] [Nonempty I] (c : ℝ) :
    finiteMean (fun _ : I => c) = c := by
  simp [finiteMean, Fintype.card_ne_zero]

theorem finiteMean_mono {I : Type*} [Fintype I] {f g : I → ℝ}
    (h : ∀ i, f i ≤ g i) : finiteMean f ≤ finiteMean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)

theorem finiteMean_sum {I J : Type*} [Fintype I] (S : Finset J) (f : J → I → ℝ) :
    finiteMean (fun i => ∑ j ∈ S, f j i) = ∑ j ∈ S, finiteMean (f j) := by
  unfold finiteMean
  rw [sum_comm, sum_div]

theorem finiteMean_mul {I : Type*} [Fintype I] (c : ℝ) (f : I → ℝ) :
    finiteMean (fun i => c * f i) = c * finiteMean f := by
  simp only [finiteMean, ← mul_sum]
  ring

theorem finiteMean_add {I : Type*} [Fintype I] (f g : I → ℝ) :
    finiteMean (fun i => f i + g i) = finiteMean f + finiteMean g := by
  simp only [finiteMean,sum_add_distrib,add_div]

theorem finiteMean_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : J → ℝ) : finiteMean (fun i => f (e i)) = finiteMean f := by
  unfold finiteMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteMean_prod {I J : Type*} [Fintype I] [Fintype J]
    (f : I × J → ℝ) : finiteMean f = finiteMean (fun i => finiteMean (fun j => f (i,j))) := by
  simp only [finiteMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, sum_div]
  simp only [div_eq_mul_inv, mul_inv_rev]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem finiteMean_split {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
    (i : V) (f : (V → B) → ℝ) :
    finiteMean f = finiteMean (fun t : B =>
      finiteMean (fun rest : {j : V // j ≠ i} → B => f ((Equiv.funSplitAt i B).symm (t,rest)))) := by
  calc
    finiteMean f = finiteMean (fun p : B × ({j : V // j ≠ i} → B) =>
      f ((Equiv.funSplitAt i B).symm p)) :=
        (finiteMean_equiv (Equiv.funSplitAt i B).symm f).symm
    _ = _ := finiteMean_prod _

theorem finiteMean_coordinate {V B : Type*} [Fintype V] [DecidableEq V]
    [Fintype B] [Nonempty B] (i : V) (g : B → ℝ) :
    finiteMean (fun lam : V → B => g (lam i)) = finiteMean g := by
  rw [finiteMean_split i]
  have he : ∀ t (rest : {j : V // j ≠ i} → B),
      ((Equiv.funSplitAt i B).symm (t,rest)) i = t := by
    intro t rest
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp_rw [he,finiteMean_const]

/-- Jensen for the logarithm, proved with its elementary tangent bound. -/
theorem finiteMean_log_le {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    finiteMean (fun i => Real.log (f i)) ≤ Real.log (finiteMean f) := by
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (0 : ℝ) < ∑ i, f i := sum_pos (fun i _ => hf i) univ_nonempty
  have hM : 0 < finiteMean f := div_pos hsum hN
  have ht : ∀ i, Real.log (f i) ≤ Real.log (finiteMean f) + f i / finiteMean f - 1 := by
    intro i
    have h := Real.log_le_sub_one_of_pos (div_pos (hf i) hM)
    rw [Real.log_div (hf i).ne' hM.ne'] at h
    linarith
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => ht i)
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at hs
  have hratio : (∑ i, f i) / finiteMean f = Fintype.card I := by
    unfold finiteMean
    field_simp
  rw [← sum_div,hratio] at hs
  exact (div_le_iff₀ hN).mpr (by nlinarith)

end LatinonEntropy

#print axioms LatinonEntropy.finiteMean_log_le
#print axioms LatinonEntropy.finiteMean_coordinate
