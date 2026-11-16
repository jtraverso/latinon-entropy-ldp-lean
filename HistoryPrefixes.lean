module

public import HistoryAbsoluteBounds
public import StoppedBudget

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

/-- The first chronological draws of a history stored newest-first. -/
def historyPrefix {Ω : Type*} (h : List Ω) (t : ℕ) : List Ω :=
  h.drop (h.length-t)

theorem historyPrefix_length {Ω : Type*} (h : List Ω) (t : ℕ) (ht : t ≤ h.length) :
    (historyPrefix h t).length = t := by
  simp only [historyPrefix,List.length_drop]
  omega

theorem historyPrefix_self {Ω : Type*} (h : List Ω) : historyPrefix h h.length = h := by
  simp [historyPrefix]

theorem historyPrefix_cons {Ω : Type*} (a : Ω) (h : List Ω) (t : ℕ) (ht : t ≤ h.length) :
    historyPrefix (a::h) t = historyPrefix h t := by
  have he : (a::h).length-t = (h.length-t)+1 := by simp only [List.length_cons]; omega
  simp only [historyPrefix,he,List.drop_succ_cons]

theorem historyPrefix_nested {Ω : Type*} (h : List Ω) (T t : ℕ)
    (ht : t ≤ T) (hT : T ≤ h.length) :
    historyPrefix (historyPrefix h T) t = historyPrefix h t := by
  rw [historyPrefix,historyPrefix_length h T hT]
  simp only [historyPrefix,List.drop_drop]
  congr 1
  omega

theorem valid_historyPrefix {n : ℕ} (h : LatinHistory n) (hv : LatinHistoryValid h)
    (t : ℕ) (ht : t ≤ h.length) : LatinHistoryValid (historyPrefix h t) := by
  induction h with
  | nil => simpa [show t = 0 by simpa using ht,historyPrefix] using hv
  | cons a h ih =>
    by_cases ht' : t ≤ h.length
    · rw [historyPrefix_cons a h t ht']; exact ih hv.1 ht'
    · have he : t = (a::h).length := by simp only [List.length_cons] at *; omega
      simpa only [he,historyPrefix_self] using hv

theorem history_first_failure {Ω : Type*} (Good : List Ω → Prop) (h : List Ω)
    (hbad : ¬historyPastLive Good h) :
    ∃ t < h.length, historyPastLive Good (historyPrefix h t) ∧
      ¬historyLive Good (historyPrefix h t) := by
  induction h with
  | nil => exact False.elim (hbad trivial)
  | cons a h ih =>
    have hstop : ¬historyLive Good h := hbad
    by_cases hpast : historyPastLive Good h
    · refine ⟨h.length,by simp,?_⟩
      simpa only [historyPrefix_cons a h h.length le_rfl,historyPrefix_self] using And.intro hpast hstop
    · obtain ⟨t,ht,hp,hs⟩ := ih hpast
      refine ⟨t,by simpa only [List.length_cons] using Nat.lt_succ_of_lt ht,?_⟩
      simpa only [historyPrefix_cons a h t ht.le] using And.intro hp hs

theorem stoppedAvailability_eq_pastLive {n : ℕ} (Good : LatinHistory n → Prop)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (hpast : historyPastLive Good h) : stoppedAvailability Good H h = availability h := by
  cases h with
  | nil => rfl
  | cons a h =>
    have hlive : historyLive Good h := hpast
    funext i j
    simp only [stoppedAvailability,hlive,ite_true]

def truncateIncrement {Ω : Type*} (T : ℕ) (X : List Ω → Ω → ℝ) (h : List Ω) (a : Ω) : ℝ :=
  if h.length < T then X h a else 0

theorem pathSum_truncate_inactive {Ω : Type*} (T : ℕ) (X : List Ω → Ω → ℝ)
    (h : List Ω) (ht : h.length ≤ T) : pathSum (truncateIncrement T X) h = pathSum X h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    have hh : h.length < T := by simp only [List.length_cons] at ht; omega
    simp only [pathSum,truncateIncrement,hh,ite_true,ih hh.le]

theorem pathSum_truncate_prefix {Ω : Type*} (T : ℕ) (X : List Ω → Ω → ℝ)
    (h : List Ω) (ht : T ≤ h.length) :
    pathSum (truncateIncrement T X) h = pathSum X (historyPrefix h T) := by
  induction h with
  | nil => have he : T = 0 := by simpa using ht
           simp [he,pathSum,historyPrefix]
  | cons a h ih =>
    by_cases hT : T ≤ h.length
    · rw [historyPrefix_cons a h T hT]
      simp only [pathSum,truncateIncrement,not_lt.mpr hT,ite_false,add_zero,ih hT]
    · have he : T = (a::h).length := by simp only [List.length_cons] at *; omega
      rw [he,historyPrefix_self]
      exact pathSum_truncate_inactive _ _ _ le_rfl

theorem pathSum_prefix_le {Ω : Type*} (X : List Ω → Ω → ℝ) (hX : ∀ g a, 0 ≤ X g a)
    (h : List Ω) (t : ℕ) (ht : t ≤ h.length) :
    pathSum X (historyPrefix h t) ≤ pathSum X h := by
  rw [← pathSum_truncate_prefix t X h ht]
  apply pathSum_mono
  intro g a
  by_cases hg : g.length < t
  · simp only [truncateIncrement,hg,ite_true]; exact le_rfl
  · simpa only [truncateIncrement,hg,ite_false] using hX g a

end LatinonEntropy

#print axioms LatinonEntropy.history_first_failure
#print axioms LatinonEntropy.stoppedAvailability_eq_pastLive
#print axioms LatinonEntropy.pathSum_truncate_prefix
