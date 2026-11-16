module

public import HistoryPropagation
public import HistoryExpectationTools

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem pathSum_abs_le {Ω : Type*} (X : List Ω → Ω → ℝ) (h : List Ω) :
    |pathSum X h| ≤ pathSum (fun g a => |X g a|) h := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih =>
    exact (abs_add_le _ _).trans (add_le_add ih le_rfl)

theorem pathSum_mono {Ω : Type*} (X Y : List Ω → Ω → ℝ)
    (hXY : ∀ h a, X h a ≤ Y h a) (h : List Ω) : pathSum X h ≤ pathSum Y h := by
  induction h with
  | nil => exact le_rfl
  | cons a h ih => exact add_le_add ih (hXY h a)

theorem pathSum_abs_le_budget {Ω : Type*} (X : List Ω → Ω → ℝ) (F : List Ω → ℝ) (b : ℝ)
    (hbound : ∀ h a, |X h a| ≤ b*F h) (h : List Ω) :
    |pathSum X h| ≤ b*pathSum (fun g (_ : Ω) => F g) h := by
  calc
    _ ≤ pathSum (fun g a => |X g a|) h := pathSum_abs_le X h
    _ ≤ pathSum (fun g (_ : Ω) => b*F g) h := pathSum_mono _ _ hbound h
    _ = _ := pathSum_mul _ _ _

theorem abs_weighted_sum_le {I : Type*} (S : Finset I) (e w : I → ℝ) (b : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ b) :
    |∑ i ∈ S, e i*w i| ≤ b*(∑ i ∈ S, |e i|) := by
  calc
    _ ≤ ∑ i ∈ S, |e i*w i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, b*|e i| := sum_le_sum (fun i hi => by
      rw [abs_mul,abs_of_nonneg (hw i hi).1]
      exact (mul_le_mul_of_nonneg_left (hw i hi).2 (abs_nonneg _)).trans_eq (mul_comm _ _))
    _ = _ := (mul_sum _ _ _).symm

theorem historyExpectation_mono_positive {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (F G : List Ω → ℝ)
    (hbound : ∀ h ∈ histories Ω T, 0 < historyWeight K h → F h ≤ G h) :
    historyExpectation K T F ≤ historyExpectation K T G := by
  apply sum_le_sum
  intro h hh
  by_cases hw : historyWeight K h = 0
  · simpa only [hw,zero_mul] using (le_refl (0 : ℝ))
  · exact mul_le_mul_of_nonneg_left
      (hbound h hh (lt_of_le_of_ne (historyWeight_nonneg K h) (Ne.symm hw))) (historyWeight_nonneg K h)

theorem history_predictable_cost_sum {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset I) (F : I → List Ω → ℝ) :
    (∑ i ∈ S, historyExpectation K T (pathSum (fun h (_ : Ω) => F i h))) =
      historyExpectation K T (pathSum (fun h (_ : Ω) => ∑ i ∈ S, F i h)) := by
  rw [← historyExpectation_sum]
  apply congrArg (historyExpectation K T)
  funext h
  exact (pathSum_sum S (fun i h (_ : Ω) => F i h) h).symm

end LatinonEntropy

#print axioms LatinonEntropy.pathSum_abs_le_budget
#print axioms LatinonEntropy.historyExpectation_mono_positive
