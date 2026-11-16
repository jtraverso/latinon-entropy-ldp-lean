module

public import LatinAvailability

@[expose] public section

/-! A predictable, absorbing live flag and the auxiliary availability that
follows the fluid after stopping. No drift bound is imposed on fallback. -/

noncomputable section

namespace LatinonEntropy

open scoped Classical

def historyLive {Ω : Type*} (Good : List Ω → Prop) : List Ω → Prop
  | [] => Good []
  | a::h => historyLive Good h ∧ Good (a::h)

theorem historyLive_tail {Ω : Type*} (Good : List Ω → Prop) (a : Ω) (h : List Ω)
    (hlive : historyLive Good (a::h)) : historyLive Good h := hlive.1

theorem historyLive_good {Ω : Type*} (Good : List Ω → Prop) (h : List Ω)
    (hlive : historyLive Good h) : Good h := by
  cases h with
  | nil => exact hlive
  | cons a h => exact hlive.2

theorem historyLive_stays_stopped {Ω : Type*} (Good : List Ω → Prop) (a : Ω) (h : List Ω)
    (hstop : ¬historyLive Good h) : ¬historyLive Good (a::h) := fun h => hstop h.1

def stoppedAvailability {n : ℕ} (Good : LatinHistory n → Prop)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) : LatinHistory n → Matrix (Fin n) (Fin n) ℝ
  | [] => availability []
  | sigma::h => fun i j => if historyLive Good h then availability (sigma::h) i j
    else stoppedAvailability Good H h i j*(1-H h.length i j)

theorem stoppedAvailability_eq_live {n : ℕ} (Good : LatinHistory n → Prop)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hlive : historyLive Good h) : stoppedAvailability Good H h = availability h := by
  cases h with
  | nil => rfl
  | cons sigma h => funext i j; simp only [stoppedAvailability,hlive.1,ite_true]

def killedRowNoise {n : ℕ} (Good : LatinHistory n → Prop)
    (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if historyLive Good h then rowPermutationMatrix sigma i j-m h i j else 0

def killedRowDrift {n : ℕ} (Good : LatinHistory n → Prop)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if historyLive Good h then m h i j-availability h i j*H h.length i j else 0

theorem stoppedAvailability_step {n : ℕ} (Good : LatinHistory n → Prop)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (hv : LatinHistoryValid (sigma::h))
    (i j : Fin n) :
    stoppedAvailability Good H (sigma::h) i j =
      stoppedAvailability Good H h i j*(1-H h.length i j)-
        killedRowNoise Good m h sigma i j-killedRowDrift Good H m h i j := by
  by_cases hlive : historyLive Good h
  · simp only [stoppedAvailability,hlive,ite_true,killedRowNoise,killedRowDrift]
    rw [stoppedAvailability_eq_live Good H h hlive]
    rw [availability_cons hv]
    ring
  · simp only [stoppedAvailability,killedRowNoise,killedRowDrift,hlive,ite_false,sub_zero]

theorem stopped_fluid_defect_step {n : ℕ} (Good : LatinHistory n → Prop)
    (H R : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (hR : ∀ t i j, R (t+1) i j = R t i j*(1-H t i j))
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (hv : LatinHistoryValid (sigma::h))
    (i j : Fin n) :
    stoppedAvailability Good H (sigma::h) i j-R (h.length+1) i j =
      (stoppedAvailability Good H h i j-R h.length i j)*(1-H h.length i j)-
        killedRowNoise Good m h sigma i j-killedRowDrift Good H m h i j := by
  rw [stoppedAvailability_step Good H m h sigma hv,hR]
  ring

end LatinonEntropy

#print axioms LatinonEntropy.historyLive_stays_stopped
#print axioms LatinonEntropy.stopped_fluid_defect_step
