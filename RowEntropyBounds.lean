module

public import PermanentalEntropy
public import PermanentalMarginals
public import FluidEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem abs_matrix_pairing_le_l1 {n : ℕ} (e g : Fin n → Fin n → ℝ) (G : ℝ)
    (hg : ∀ i j, |g i j| ≤ G) :
    |∑ i, ∑ j, e i j*g i j| ≤ G*(∑ i, ∑ j, |e i j|) := by
  calc
    _ ≤ ∑ i, |∑ j, e i j*g i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |e i j*g i j| := sum_le_sum (fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |e i j| * G := sum_le_sum (fun i _ => sum_le_sum (fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg _)))
    _ = (∑ i, ∑ j, |e i j|)*G := by simp only [sum_mul]
    _ = _ := mul_comm _ _

def centeredEntryLog {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  if Q i j = 0 then 0 else -Real.log (Q i j)-Real.log (n : ℝ)

theorem permanental_entropy_log_band {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hper : Q.permanent ≠ 0) (hrow : ∀ i, ∑ j, Q i j = 1)
    (G : ℝ) (hG : 0 ≤ G)
    (hband : ∀ i j, Q i j ≠ 0 → |-Real.log (Q i j)-Real.log (n : ℝ)| ≤ G) :
    matrixEntropy Q+Real.log Q.permanent-G*(∑ i, ∑ j, |permanentMarginal Q i j-Q i j|) ≤
      permanentalEntropy Q := by
  have hmass : (∑ i, ∑ j, (permanentMarginal Q i j-Q i j)) = 0 := by
    simp only [sum_sub_distrib,permanentMarginal_row Q hper,hrow,sub_self,sum_const_zero]
  have hpoint : ∀ i j,
      (permanentMarginal Q i j-Q i j)*(-Real.log (Q i j)) =
        (permanentMarginal Q i j-Q i j)*centeredEntryLog Q i j+
          (permanentMarginal Q i j-Q i j)*Real.log (n : ℝ) := by
    intro i j
    by_cases hz : Q i j = 0
    · rw [permanentMarginal_zero_of_entry_zero Q i j hz,hz]
      simp only [sub_self,zero_mul,add_zero]
    · simp only [centeredEntryLog,hz,ite_false]; ring
  have hcenter : (∑ i, ∑ j, (permanentMarginal Q i j-Q i j)*(-Real.log (Q i j))) =
      ∑ i, ∑ j, (permanentMarginal Q i j-Q i j)*centeredEntryLog Q i j := by
    simp_rw [hpoint]
    simp only [sum_add_distrib,← sum_mul,hmass,zero_mul,add_zero]
  have hg : ∀ i j, |centeredEntryLog Q i j| ≤ G := by
    intro i j
    by_cases hz : Q i j = 0
    · simpa only [centeredEntryLog,hz,ite_true,abs_zero] using hG
    · simpa only [centeredEntryLog,hz,ite_false] using hband i j hz
  have herr := abs_matrix_pairing_le_l1 (fun i j => permanentMarginal Q i j-Q i j) (centeredEntryLog Q) G hg
  have hlo := neg_abs_le (∑ i, ∑ j, (permanentMarginal Q i j-Q i j)*centeredEntryLog Q i j)
  have hpair : (∑ i, ∑ j, permanentMarginal Q i j*(-Real.log (Q i j))) =
      matrixEntropy Q+(∑ i, ∑ j, (permanentMarginal Q i j-Q i j)*(-Real.log (Q i j))) := by
    unfold matrixEntropy
    simp only [sub_mul,sum_sub_distrib,mul_neg,sum_neg_distrib]
    ring
  have he := permanental_entropy_eq Q hper
  rw [hpair,hcenter] at he
  linarith only [he,herr,hlo]

theorem permanental_entropy_lower {n : ℕ} (hn : 0 < n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (c : ℝ) (hcap : ∀ i j, Q i j ≤ c/n) (m : ℕ) (hm : Real.exp 2*c ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (G : ℝ) (hG : 0 ≤ G)
    (hband : ∀ i j, Q i j ≠ 0 → |-Real.log (Q i j)-Real.log (n : ℝ)| ≤ G) :
    matrixEntropy Q-(n : ℝ)-G*Real.sqrt (2*(n : ℝ)*permanentCapError m n) ≤ permanentalEntropy Q := by
  have hp := doubly_stochastic_permanent_log_lower hn Q hQ hrow hcol
  have he := permanental_entropy_log_band Q hp.1.ne' hrow G hG hband
  have hmarg := permanental_marginal_l1_le hn m c Q hQ hrow hcol hcap hm hsize
  have hmul := mul_le_mul_of_nonneg_left hmarg hG
  linarith only [hp.2,he,hmul]

end LatinonEntropy

#print axioms LatinonEntropy.permanental_entropy_lower
