module

public import HistoryPrefixes

@[expose] public section

noncomputable section

namespace LatinonEntropy

theorem pathSum_congr_before {Ω : Type*} (X Y : List Ω → Ω → ℝ) (T : ℕ)
    (heq : ∀ g, g.length < T → ∀ a, X g a = Y g a)
    (h : List Ω) (hlen : h.length ≤ T) : pathSum X h = pathSum Y h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    have ht : h.length < T := by simp only [List.length_cons] at hlen; omega
    rw [pathSum,pathSum,ih ht.le,heq h ht a]

theorem pathSum_local_to_prefix {Ω : Type*} (X : List Ω → Ω → ℝ) (T : ℕ)
    (hzero : ∀ g, T ≤ g.length → ∀ a, X g a = 0)
    (h : List Ω) (hlen : T ≤ h.length) :
    pathSum X h = pathSum X (historyPrefix h T) := by
  rw [← pathSum_truncate_prefix T X h hlen]
  apply pathSum_congr
  intro g a
  by_cases hg : g.length < T
  · simp only [truncateIncrement,hg,ite_true]
  · simp only [truncateIncrement,hg,ite_false,hzero g (not_lt.mp hg) a]

end LatinonEntropy

#print axioms LatinonEntropy.pathSum_local_to_prefix
