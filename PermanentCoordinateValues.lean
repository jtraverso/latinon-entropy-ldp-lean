module

public import LatinRowPolicy
public import HistoryNoise

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem permanentMarginal_row_value {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (v : Fin n → ℝ) :
    (∑ j, permanentMarginal Q i j*v j) = ∑ sigma, permanentLaw Q sigma*v (sigma i) := by
  unfold permanentMarginal
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro sigma _
  simp only [ite_mul,zero_mul]
  simp

theorem permanentMarginal_col_value {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (v : Fin n → ℝ) :
    (∑ i, permanentMarginal Q i j*v i) = ∑ sigma, permanentLaw Q sigma*v (sigma.symm j) := by
  unfold permanentMarginal
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro sigma _
  have he : ∀ i, sigma i = j ↔ i = sigma.symm j := by
    intro i
    constructor
    · intro h
      simpa using congrArg sigma.symm h
    · intro h
      subst i
      simp
  simp only [ite_mul,zero_mul]
  simp_rw [he]
  simp

theorem rowPermutationMatrix_row_value {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (i : Fin n) (v : Fin n → ℝ) : (∑ j, rowPermutationMatrix sigma i j*v j) = v (sigma i) := by
  simp [rowPermutationMatrix]

theorem rowPermutationMatrix_col_value {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (j : Fin n) (v : Fin n → ℝ) : (∑ i, rowPermutationMatrix sigma i j*v i) = v (sigma.symm j) := by
  have he : ∀ i, sigma i = j ↔ i = sigma.symm j := by
    intro i
    constructor
    · intro h
      simpa using congrArg sigma.symm h
    · intro h
      subst i
      simp
  simp only [rowPermutationMatrix,ite_mul,one_mul,zero_mul]
  simp_rw [he]
  simp

theorem killed_row_noise_value {n : ℕ} (hn : 0 < n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (w : LatinHistory n → Fin n → ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ j, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j*w h j) =
      killedCenteredValue (S.kernel hn) Good (fun g tau => w g (tau i)) h sigma := by
  by_cases hlive : historyLive Good h
  · simp only [killedRowNoise,killedCenteredValue,hlive,ite_true,sub_mul,sum_sub_distrib,LatinRowPolicy.kernel]
    rw [rowPermutationMatrix_row_value,permanentMarginal_row_value]
  · simp only [killedRowNoise,killedCenteredValue,hlive,ite_false,zero_mul,sum_const_zero]

theorem killed_col_noise_value {n : ℕ} (hn : 0 < n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (w : LatinHistory n → Fin n → ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (j : Fin n) :
    (∑ i, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j*w h i) =
      killedCenteredValue (S.kernel hn) Good (fun g tau => w g (tau.symm j)) h sigma := by
  by_cases hlive : historyLive Good h
  · simp only [killedRowNoise,killedCenteredValue,hlive,ite_true,sub_mul,sum_sub_distrib,LatinRowPolicy.kernel]
    rw [rowPermutationMatrix_col_value,permanentMarginal_col_value]
  · simp only [killedRowNoise,killedCenteredValue,hlive,ite_false,zero_mul,sum_const_zero]

end LatinonEntropy

#print axioms LatinonEntropy.killed_row_noise_value
#print axioms LatinonEntropy.killed_col_noise_value
