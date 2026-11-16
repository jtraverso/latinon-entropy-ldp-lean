module

public import HistoryMartingale
public import FluidStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem pathSum_add {Ω : Type*} (X Y : List Ω → Ω → ℝ) (h : List Ω) :
    pathSum (fun g a => X g a+Y g a) h = pathSum X h+pathSum Y h := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih => simp only [pathSum,ih]; ring

theorem pathSum_mul {Ω : Type*} (c : ℝ) (X : List Ω → Ω → ℝ) (h : List Ω) :
    pathSum (fun g a => c*X g a) h = c*pathSum X h := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih => simp only [pathSum,ih]; ring

theorem pathSum_sum {Ω I : Type*} (S : Finset I) (X : I → List Ω → Ω → ℝ) (h : List Ω) :
    pathSum (fun g a => ∑ i ∈ S, X i g a) h = ∑ i ∈ S, pathSum (X i) h := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih => simp only [pathSum,ih,sum_add_distrib]

theorem pathSum_congr {Ω : Type*} (X Y : List Ω → Ω → ℝ)
    (heq : ∀ h a, X h a = Y h a) (h : List Ω) : pathSum X h = pathSum Y h := by
  induction h with
  | nil => rfl
  | cons a h ih => rw [pathSum,pathSum,ih,heq]

/-- Exact propagation along a valid history, keeping a deterministic future
horizon. This avoids introducing independent copies of different prefixes. -/
theorem history_defect_propagation {Ω : Type*} (Valid : List Ω → Prop)
    (htail : ∀ a h, Valid (a::h) → Valid h) (D : List Ω → ℝ) (H : ℕ → ℝ)
    (E : List Ω → Ω → ℝ) (hzero : D [] = 0)
    (hstep : ∀ a h, Valid (a::h) → D (a::h) = D h*(1-H h.length)-E h a)
    (h : List Ω) (hv : Valid h) (T : ℕ) (hlen : h.length ≤ T) :
    D h*(∏ k ∈ Ico h.length T, (1-H k)) =
      -pathSum (fun g a => propagationKernel H g.length T*E g a) h := by
  induction h generalizing T with
  | nil => simp [hzero,pathSum]
  | cons a h ih =>
    have ht : h.length < T := by simpa using hlen
    have hp : (∏ k ∈ Ico h.length T, (1-H k)) =
        (1-H h.length)*propagationKernel H h.length T :=
      prod_eq_prod_Ico_succ_bot ht _
    have hprev := ih (htail a h hv) T ht.le
    rw [hp] at hprev
    change D (a::h)*propagationKernel H h.length T =
      -(pathSum (fun g a => propagationKernel H g.length T*E g a) h+
        propagationKernel H h.length T*E h a)
    rw [hstep a h hv]
    calc
      _ = D h*((1-H h.length)*propagationKernel H h.length T)-
          propagationKernel H h.length T*E h a := by ring
      _ = _ := by rw [hprev]; ring

theorem history_defect_at_horizon {Ω : Type*} (Valid : List Ω → Prop)
    (htail : ∀ a h, Valid (a::h) → Valid h) (D : List Ω → ℝ) (H : ℕ → ℝ)
    (E : List Ω → Ω → ℝ) (hzero : D [] = 0)
    (hstep : ∀ a h, Valid (a::h) → D (a::h) = D h*(1-H h.length)-E h a)
    (h : List Ω) (hv : Valid h) :
    D h = -pathSum (fun g a => propagationKernel H g.length h.length*E g a) h := by
  simpa using history_defect_propagation Valid htail D H E hzero hstep h hv h.length le_rfl

end LatinonEntropy

#print axioms LatinonEntropy.history_defect_at_horizon
