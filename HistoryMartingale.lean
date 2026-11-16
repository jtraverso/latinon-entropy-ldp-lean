module

public import FiniteHistory

@[expose] public section

/-! Conditional sums are expanded on the actual finite history tree. The
MGF iteration and second-moment estimate do not assume independence. -/

noncomputable section

namespace LatinonEntropy

open Finset

def pathSum {Ω : Type*} (Z : List Ω → Ω → ℝ) : List Ω → ℝ
  | [] => 0
  | a::h => pathSum Z h+Z h a

theorem history_mgf_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (v : ℕ → ℝ) (lambda : ℝ)
    (hstep : ∀ h, (∑ a, K.transition h a*Real.exp (lambda*Z h a)) ≤ Real.exp (v h.length))
    (t : ℕ) :
    historyExpectation K t (fun h => Real.exp (lambda*pathSum Z h)) ≤
      Real.exp (∑ s ∈ range t, v s) := by
  induction t with
  | zero => simp [historyExpectation,histories,historyWeight,pathSum]
  | succ t ih =>
    rw [historyExpectation_tower]
    calc
      _ ≤ historyExpectation K t (fun h => Real.exp (v t)*Real.exp (lambda*pathSum Z h)) := by
        apply historyExpectation_mono
        intro h hh
        have he : (∑ a, K.transition h a*Real.exp (lambda*pathSum Z (a::h))) =
            Real.exp (lambda*pathSum Z h)*(∑ a, K.transition h a*Real.exp (lambda*Z h a)) := by
          simp only [pathSum,mul_add,Real.exp_add,mul_sum]
          apply sum_congr rfl
          intro a _
          ring
        rw [he]
        have hs := hstep h
        rw [histories_length hh] at hs
        exact (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le).trans_eq (mul_comm _ _)
      _ = Real.exp (v t)*historyExpectation K t (fun h => Real.exp (lambda*pathSum Z h)) :=
        historyExpectation_mul K t _ _
      _ ≤ Real.exp (v t)*Real.exp (∑ s ∈ range t, v s) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add,sum_range_succ]; congr 1; ring

theorem history_pathSum_mean_zero {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ)
    (hzero : ∀ h, ∑ a, K.transition h a*Z h a = 0) (t : ℕ) :
    historyExpectation K t (pathSum Z) = 0 := by
  induction t with
  | zero => simp [historyExpectation,histories,pathSum]
  | succ t ih =>
    rw [historyExpectation_tower]
    have he : ∀ h, (∑ a, K.transition h a*pathSum Z (a::h)) = pathSum Z h := by
      intro h
      simp only [pathSum,mul_add,sum_add_distrib,← sum_mul,K.total,hzero,one_mul,add_zero]
    simp_rw [he]
    exact ih

theorem finite_centered_square {Ω : Type*} [Fintype Ω]
    (p Z : Ω → ℝ) (hmass : ∑ a, p a = 1) (hzero : ∑ a, p a*Z a = 0) (s : ℝ) :
    (∑ a, p a*(s+Z a)^2) = s^2+∑ a, p a*(Z a)^2 := by
  have he : ∀ a, p a*(s+Z a)^2 = p a*s^2+(2*s)*(p a*Z a)+p a*(Z a)^2 := by
    intro a
    ring
  simp only [he,sum_add_distrib,← sum_mul,← mul_sum,hmass,hzero,
    one_mul,mul_zero,add_zero]

theorem history_pathSum_second_moment_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (v : ℕ → ℝ)
    (hzero : ∀ h, ∑ a, K.transition h a*Z h a = 0)
    (hvar : ∀ h, (∑ a, K.transition h a*(Z h a)^2) ≤ v h.length) (t : ℕ) :
    historyExpectation K t (fun h => (pathSum Z h)^2) ≤ ∑ s ∈ range t, v s := by
  induction t with
  | zero => simp [historyExpectation,histories,pathSum]
  | succ t ih =>
    rw [historyExpectation_tower]
    calc
      _ ≤ historyExpectation K t (fun h => (pathSum Z h)^2+v t) := by
        apply historyExpectation_mono
        intro h hh
        change (∑ a, K.transition h a*(pathSum Z h+Z h a)^2) ≤ _
        rw [finite_centered_square _ _ (K.total h) (hzero h)]
        have hv := hvar h
        rw [histories_length hh] at hv
        exact add_le_add le_rfl hv
      _ = historyExpectation K t (fun h => (pathSum Z h)^2)+v t := by
        rw [historyExpectation_add,historyExpectation_const]
      _ ≤ (∑ s ∈ range t, v s)+v t := add_le_add ih le_rfl
      _ = _ := (sum_range_succ _ _).symm

end LatinonEntropy

#print axioms LatinonEntropy.history_mgf_le
#print axioms LatinonEntropy.history_pathSum_second_moment_le
