module

public import WeightedLogSum

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- The entropy of a nonempty block is maximized by its constant vector,
including the case where the block has zero total mass. -/
theorem finite_block_entropy_upper {I : Type*} [DecidableEq I]
    (S : Finset I) (hS : S.Nonempty) (x : I → ℝ) (hx : ∀ i ∈ S, 0 ≤ x i) :
    -(∑ i ∈ S, x i*Real.log (x i)) ≤
      (∑ i ∈ S, x i)*Real.log (S.card : ℝ)-
        (∑ i ∈ S, x i)*Real.log (∑ i ∈ S, x i) := by
  by_cases hzero : (∑ i ∈ S, x i) = 0
  · have hz : ∀ i ∈ S, x i = 0 := by
      intro i hi
      have hle := Finset.single_le_sum (f := x) hx hi
      rw [hzero] at hle
      exact le_antisymm hle (hx i hi)
    have hlog : (∑ i ∈ S, x i*Real.log (x i)) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [hz i hi]
      simp
    rw [hlog,hzero]
    simp
  · have hpos : 0 < ∑ i ∈ S, x i :=
      lt_of_le_of_ne (sum_nonneg hx) (Ne.symm hzero)
    have hsum : ∀ f : I → ℝ, (∑ i : S, f i.val) = ∑ i ∈ S, f i := by
      intro f
      rw [← attach_eq_univ,sum_attach]
    have htotal : 0 < ∑ i : S, x i.val := by rw [hsum]; exact hpos
    have hN : 0 < ∑ _i : S, (1 : ℝ) := by
      simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] using
        (Nat.cast_pos.mpr (card_pos.mpr hS) : (0 : ℝ) < S.card)
    have hg := unnormalized_gibbs (fun i : S => x i.val) (fun _ => (1 : ℝ))
      (fun i => hx i.val i.property) (fun _ => zero_le_one) htotal hN (fun _ _ => zero_lt_one)
    simp only [Real.log_one,mul_zero,sum_const_zero,neg_zero,zero_add,
      sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one] at hg
    rw [hsum x,hsum (fun i => x i*Real.log (x i))] at hg
    linarith only [hg]

end LatinonEntropy

#print axioms LatinonEntropy.finite_block_entropy_upper
