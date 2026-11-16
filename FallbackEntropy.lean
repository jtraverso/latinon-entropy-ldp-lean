module

public import HistoryEntropy
public import PermanentalEntropy
public import MainRangeParameters

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem kernel_transition_le_one {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω) (h : List Ω) (a : Ω) :
    K.transition h a ≤ 1 := by
  simpa only [K.total] using single_le_sum (fun b _ => K.nonneg h b) (mem_univ a)

theorem kernelEntropy_nonneg {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω) (h : List Ω) :
    0 ≤ kernelEntropy K h := by
  exact neg_nonneg.mpr (sum_nonpos (fun a _ => mul_nonpos_of_nonneg_of_nonpos (K.nonneg h a)
    (Real.log_nonpos (K.nonneg h a) (kernel_transition_le_one K h a))))

theorem permanental_entropy_two_values {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hper : Q.permanent ≠ 0) (w : ℝ) (hvalues : ∀ i j, Q i j = 0 ∨ Q i j = w) :
    permanentalEntropy Q = -(n : ℝ)*Real.log w+Real.log Q.permanent := by
  have hp : ∀ i j, permanentMarginal Q i j*(-Real.log (Q i j)) = permanentMarginal Q i j*(-Real.log w) := by
    intro i j
    rcases hvalues i j with hz | hw
    · rw [permanentMarginal_zero_of_entry_zero Q i j hz]
      simp only [zero_mul]
    · rw [hw]
  rw [permanental_entropy_eq Q hper]
  simp_rw [hp]
  simp only [← sum_mul,permanentMarginal_row Q hper,one_mul,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem fallback_row_entropy_lower {n : ℕ} (hn : 0 < n) (h : LatinHistory n)
    (hv : LatinHistoryValid h) (ht : h.length < n) :
    (n : ℝ)*Real.log ((n : ℝ)-h.length)-(n : ℝ) ≤ permanentalEntropy (fallbackRowMatrix n h) := by
  have hk : 0 < (n : ℝ)-h.length := sub_pos.mpr (Nat.cast_lt.mpr ht)
  have hvalues : ∀ i j, fallbackRowMatrix n h i j = 0 ∨
      fallbackRowMatrix n h i j = 1/((n : ℝ)-h.length) := by
    intro i j
    rcases availability_binary h i j with hz | ho
    · left; simp only [fallbackRowMatrix,hv,ht,and_self,ite_true,hz,zero_div]
    · right; simp only [fallbackRowMatrix,hv,ht,and_self,ite_true,ho]
  have hper := doubly_stochastic_permanent_log_lower hn (fallbackRowMatrix n h)
    (fallbackRowMatrix_nonneg h) (fallbackRowMatrix_row hn h) (fallbackRowMatrix_col hn h)
  have he := permanental_entropy_two_values (fallbackRowMatrix n h) hper.1.ne'
    (1/((n : ℝ)-h.length)) hvalues
  rw [Real.log_div one_ne_zero hk.ne',Real.log_one,zero_sub] at he
  linarith only [he,hper.2]

theorem profile_policy_fallback_after_main {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (h : LatinHistory n) (hlen : mainRange eps n < h.length) :
    (profileProcessPolicy P eps heps budget).matrix h = fallbackRowMatrix n h := by
  have hlenR : (mainRange eps n : ℝ)+1 ≤ h.length := by exact_mod_cast (Nat.succ_le_iff.mpr hlen)
  have hx : (1-eps)*(n : ℝ) < h.length := (Nat.lt_floor_add_one _).trans_le hlenR
  have hdegree : ¬eps*n ≤ (n : ℝ)-h.length := by intro hd; nlinarith only [hd,hx]
  have hstop : ¬historyLive (profileProcessGood P eps heps budget) h := by
    intro hlive
    have hc := (historyLive_good (profileProcessGood P eps heps budget) h hlive).1
    exact hdegree hc.degree
  exact latinStoppedPolicy_fallback P.npos (profileCorrectionParameters P eps heps) (profileCandidate P) budget h hstop

theorem profile_tail_kernel_entropy_lower {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (h : LatinHistory n)
    (hv : LatinHistoryValid h) (ht : h.length < n) (hlen : mainRange eps n < h.length) :
    (n : ℝ)*Real.log ((n : ℝ)-h.length)-(n : ℝ) ≤
      kernelEntropy ((profileProcessPolicy P eps heps budget).kernel P.npos) h := by
  rw [row_kernel_entropy_eq,profile_policy_fallback_after_main P eps heps budget h hlen]
  exact fallback_row_entropy_lower P.npos h hv ht

end LatinonEntropy

#print axioms LatinonEntropy.kernelEntropy_nonneg
#print axioms LatinonEntropy.profile_tail_kernel_entropy_lower
