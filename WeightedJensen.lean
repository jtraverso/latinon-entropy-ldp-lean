module

public import FiniteAverages

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem finite_exp_jensen {I : Type*} [Fintype I]
    (p X : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1) :
    (∑ i, p i * X i) ≤ Real.log (∑ i, p i * Real.exp (X i)) := by
  have hex : ∃ i, 0 < p i := by
    by_contra! h
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => h i)
    simp only [sum_const_zero,hmass] at hs
    linarith
  obtain ⟨i,hi⟩ := hex
  let M := ∑ i, p i * Real.exp (X i)
  have hM : 0 < M := lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
    (single_le_sum (fun j _ => mul_nonneg (hp j) (Real.exp_pos _).le) (mem_univ i))
  have ht : ∀ i, p i * (X i - Real.log M) ≤ p i * (Real.exp (X i) / M - 1) := by
    intro i
    have h := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (X i)) hM)
    rw [Real.log_div (Real.exp_pos _).ne' hM.ne',Real.log_exp] at h
    exact mul_le_mul_of_nonneg_left h (hp i)
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => ht i)
  have hleft : (∑ i, p i * (X i - Real.log M)) = (∑ i, p i * X i) - Real.log M := by
    rw [show (∑ i, p i * (X i - Real.log M)) =
      (∑ i, p i * X i) - (∑ i, p i * Real.log M) by simp only [mul_sub,sum_sub_distrib]]
    rw [← sum_mul,hmass,one_mul]
  have hright : (∑ i, p i * (Real.exp (X i) / M - 1)) = 0 := by
    simp only [mul_sub,← mul_div_assoc,mul_one,sum_sub_distrib,← sum_div,hmass]
    change M / M - 1 = 0
    simp [hM.ne']
  rw [hleft,hright] at hs
  change (∑ i, p i * X i) ≤ Real.log M
  linarith

/-- Optimization restricted to |t| <= 1. The size condition on d is explicit. -/
theorem quadratic_moment_bound {N d L : ℝ}
    (hN : 0 < N) (hd : 0 ≤ d) (hdN : d ≤ N/2) (hL : 0 ≤ L)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t*L ≤ N*t^2/2+d) :
    L ≤ Real.sqrt (2*N*d) := by
  have h1 := h 1 zero_le_one le_rfl
  have hLN : L ≤ N := by nlinarith
  have ht0 : 0 ≤ L/N := div_nonneg hL hN.le
  have ht1 : L/N ≤ 1 := (div_le_one hN).mpr hLN
  have hopt := h (L/N) ht0 ht1
  have he : (L/N)*L - N*(L/N)^2/2 = L^2/(2*N) := by field_simp; ring
  have hdiv : L^2/(2*N) ≤ d := by linarith [hopt,he]
  have hs0 := (div_le_iff₀ (by positivity : 0 < 2*N)).mp hdiv
  have hs : L^2 ≤ 2*N*d := by nlinarith
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 2*N*d)
  have hroot0 := Real.sqrt_nonneg (2*N*d)
  nlinarith

end LatinonEntropy

#print axioms LatinonEntropy.finite_exp_jensen
#print axioms LatinonEntropy.quadratic_moment_bound
