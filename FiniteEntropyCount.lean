module

public import FiniteCore

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Entropy-to-count using one positive reference weight outside the good
set. Zero atoms are allowed and there is no division by the good mass. -/
theorem finite_entropy_to_good_count {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1)
    (S : Finset I) (hS : S.Nonempty) (L : ℝ)
    (hcap : (Fintype.card I : ℝ)*Real.exp (-L) ≤ 1) :
    -(∑ i, p i*Real.log (p i))-(∑ i, if i ∈ S then 0 else p i)*L-Real.log 2 ≤ Real.log (S.card : ℝ) := by
  let r : I → ℝ := fun i => if i ∈ S then 1 else Real.exp (-L)
  have hr : ∀ i, 0 < r i := by intro i; unfold r; split_ifs; norm_num; exact Real.exp_pos _
  obtain ⟨i0,hi0⟩ := hS
  have hpos : 0 < ∑ i, r i := (hr i0).trans_le (single_le_sum (fun i _ => (hr i).le) (mem_univ i0))
  have hScard : (1 : ℝ) ≤ S.card := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_pos.mpr ⟨i0,hi0⟩))
  have hSpos : (0 : ℝ) < S.card := by linarith only [hScard]
  have hcard : (∑ i : I, if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    rw [← sum_filter]
    simp
  have hsum : (∑ i, r i) ≤ (S.card : ℝ)+1 := by
    calc
      _ ≤ ∑ i, ((if i ∈ S then (1 : ℝ) else 0)+Real.exp (-L)) := by
        apply sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simp only [r,hi,ite_true]
          linarith only [(Real.exp_pos (-L))]
        · simp only [r,hi,ite_false,zero_add,le_refl]
      _ = (S.card : ℝ)+(Fintype.card I : ℝ)*Real.exp (-L) := by rw [sum_add_distrib,hcard]; simp
      _ ≤ _ := add_le_add le_rfl hcap
  have hupper : (∑ i, r i) ≤ 2*(S.card : ℝ) := by linarith only [hsum,hScard]
  have hg := finite_gibbs p r hp (fun i => (hr i).le) htotal (fun i _ => hr i) hpos
  have hs : -(∑ i, p i*Real.log (r i)) = (∑ i, if i ∈ S then 0 else p i)*L := by
    rw [← sum_neg_distrib,sum_mul]
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp only [r,hi,ite_true,Real.log_one,mul_zero,neg_zero,zero_mul]
    · simp only [r,hi,ite_false,Real.log_exp]
      ring
  have hl := Real.log_le_log hpos hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hSpos.ne'] at hl
  rw [hs] at hg
  linarith only [hg,hl]

end LatinonEntropy

#print axioms LatinonEntropy.finite_entropy_to_good_count
