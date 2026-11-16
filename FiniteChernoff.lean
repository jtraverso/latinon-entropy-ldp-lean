module

public import WeightedJensen

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem finite_exponential_sum_pos {I : Type*} [Fintype I]
    (p X : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    0 < ∑ i, p i * Real.exp (X i) := by
  have hex : ∃ i, 0 < p i := by
    by_contra! h
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => h i)
    simp only [sum_const_zero,hmass] at hs
    linarith
  obtain ⟨i,hi⟩ := hex
  exact lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
    (single_le_sum (fun j _ => mul_nonneg (hp j) (Real.exp_pos _).le) (mem_univ i))

theorem finite_chernoff_one_side {I : Type*} [Fintype I]
    (p X : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (t u A : ℝ) (ht : 0 ≤ t)
    (hlog : Real.log (∑ i, p i * Real.exp (t*X i)) ≤ A) :
    (∑ i, if u ≤ X i then p i else 0) ≤ Real.exp (A-t*u) := by
  classical
  have hpoint : ∀ i, (if u ≤ X i then p i else 0) * Real.exp (t*u) ≤
      p i * Real.exp (t*X i) := by
    intro i
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ht)) (hp i)
    · simp only [zero_mul]
      exact mul_nonneg (hp i) (Real.exp_pos _).le
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hpoint i)
  rw [← sum_mul] at hs
  have hm := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (finite_exponential_sum_pos p (fun i => t*X i) hp hmass)] at hm
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (hs.trans hm)

theorem finite_chernoff_two_sided {I : Type*} [Fintype I]
    (p X : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (N d u : ℝ) (hN : 0 < N) (hu0 : 0 ≤ u) (huN : u ≤ N)
    (hlog : ∀ t : ℝ, |t| ≤ 1 →
      Real.log (∑ i, p i * Real.exp (t*X i)) ≤ N*t^2/2+d) :
    (∑ i, if u ≤ |X i| then p i else 0) ≤ 2*Real.exp (d-u^2/(2*N)) := by
  classical
  let t := u/N
  have ht0 : 0 ≤ t := div_nonneg hu0 hN.le
  have ht1 : t ≤ 1 := (div_le_one hN).mpr huN
  have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith,ht1⟩
  have hplus := finite_chernoff_one_side p X hp hmass t u (N*t^2/2+d) ht0 (hlog t habs)
  have hm : Real.log (∑ i, p i * Real.exp (t*(-X i))) ≤ N*t^2/2+d := by
    have h := hlog (-t) (by simpa using habs)
    simpa only [neg_mul,mul_neg,neg_sq] using h
  have hminus := finite_chernoff_one_side p (fun i => -X i) hp hmass t u
    (N*t^2/2+d) ht0 hm
  have he : N*t^2/2+d-t*u = d-u^2/(2*N) := by dsimp [t]; field_simp; ring
  rw [he] at hplus hminus
  have hpoint : ∀ i, (if u ≤ |X i| then p i else 0) ≤
      (if u ≤ X i then p i else 0) + (if u ≤ -X i then p i else 0) := by
    intro i
    by_cases h0 : u ≤ |X i|
    · have hor : u ≤ X i ∨ u ≤ -X i := by
        by_cases hx : 0 ≤ X i
        · exact Or.inl (by simpa only [abs_of_nonneg hx] using h0)
        · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hx)] using h0)
      rcases hor with h | h <;> simp only [h0,ite_true,h] <;> split_ifs <;> linarith [hp i]
    · simp only [h0,ite_false]
      split_ifs <;> linarith [hp i]
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hpoint i)
  rw [sum_add_distrib] at hs
  linarith

end LatinonEntropy

#print axioms LatinonEntropy.finite_chernoff_two_sided
