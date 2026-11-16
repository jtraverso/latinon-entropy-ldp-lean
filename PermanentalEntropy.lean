module

public import HistoryEntropy
public import LatinRowPolicy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def permanentalEntropy {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -∑ sigma, permanentLaw Q sigma*Real.log (permanentLaw Q sigma)

def matrixEntropy {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -∑ i, ∑ j, Q i j*Real.log (Q i j)

theorem permanentMarginal_zero_of_entry_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hz : Q i j = 0) : permanentMarginal Q i j = 0 := by
  have hweight : ∀ sigma : Equiv.Perm (Fin n), sigma i = j → permWeight Q sigma = 0 := by
    intro sigma he
    unfold permWeight
    exact prod_eq_zero (mem_univ i) (by rw [he,hz])
  unfold permanentMarginal
  apply sum_eq_zero
  intro sigma _
  split_ifs with he
  · simp only [permanentLaw,hweight sigma he,zero_div]
  · rfl

/-- Exact row entropy, with zero-probability permutations retained. -/
theorem permanental_entropy_eq {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hper : Q.permanent ≠ 0) :
    permanentalEntropy Q = (∑ i, ∑ j, permanentMarginal Q i j*(-Real.log (Q i j)))+Real.log Q.permanent := by
  have hlocal : ∀ sigma : Equiv.Perm (Fin n),
      -(permanentLaw Q sigma*Real.log (permanentLaw Q sigma)) =
        permanentLaw Q sigma*permutationStatistic (fun i j => -Real.log (Q i j)) sigma+
          permanentLaw Q sigma*Real.log Q.permanent := by
    intro sigma
    by_cases hw : permWeight Q sigma = 0
    · simp only [permanentLaw,hw,zero_div,zero_mul,neg_zero,add_zero]
    · have hentry : ∀ i ∈ (univ : Finset (Fin n)), Q i (sigma i) ≠ 0 :=
        prod_ne_zero_iff.mp hw
      have hlog : Real.log (permanentLaw Q sigma) = (∑ i, Real.log (Q i (sigma i)))-Real.log Q.permanent := by
        rw [permanentLaw,Real.log_div hw hper]
        exact congrArg (fun x : ℝ => x-Real.log Q.permanent) (Real.log_prod hentry)
      rw [hlog]
      simp only [permutationStatistic,sum_neg_distrib]
      ring
  unfold permanentalEntropy
  rw [← sum_neg_distrib]
  simp_rw [hlocal]
  rw [sum_add_distrib,← permanentMarginal_pairing,← sum_mul,sum_permanentLaw Q hper,one_mul]

theorem row_kernel_entropy_eq {n : ℕ} (S : LatinRowPolicy n) (hn : 0 < n) (h : LatinHistory n) :
    kernelEntropy (S.kernel hn) h = permanentalEntropy (S.matrix h) := rfl

end LatinonEntropy

#print axioms LatinonEntropy.permanental_entropy_eq
#print axioms LatinonEntropy.row_kernel_entropy_eq
