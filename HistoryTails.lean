module

public import StoppedRowPolicy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

/-- Finite conditional Chernoff on the actual history distribution. -/
theorem history_deviation_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (N d : ℝ) (hN : 0 < N)
    (hstep : ∀ lambda : ℝ, |lambda| ≤ 1 → ∀ h,
      (∑ a, K.transition h a*Real.exp (lambda*Z h a)) ≤ Real.exp (N*lambda^2/2+d))
    (T : ℕ) (hT : 0 < T) (u : ℝ) (hu0 : 0 ≤ u) (huT : u ≤ (T : ℝ)*N) :
    (∑ h ∈ histories Ω T, if u ≤ |pathSum Z h| then historyWeight K h else 0) ≤
      2*Real.exp ((T : ℝ)*d-u^2/(2*((T : ℝ)*N))) := by
  let S := histories Ω T
  let p : S → ℝ := fun h => historyWeight K h
  let X : S → ℝ := fun h => pathSum Z h
  have hp : ∀ h, 0 ≤ p h := fun h => historyWeight_nonneg K h
  have hmass : (∑ h : S, p h) = 1 := by
    change (∑ h : S, historyWeight K h) = 1
    rw [Finset.sum_coe_sort]
    exact historyWeight_total K T
  have hlog : ∀ lambda : ℝ, |lambda| ≤ 1 →
      Real.log (∑ h : S, p h*Real.exp (lambda*X h)) ≤
        ((T : ℝ)*N)*lambda^2/2+(T : ℝ)*d := by
    intro lambda hlambda
    have hmgf := history_mgf_le K Z (fun _ => N*lambda^2/2+d) lambda (hstep lambda hlambda) T
    have he : (∑ h : S, p h*Real.exp (lambda*X h)) =
        historyExpectation K T (fun h => Real.exp (lambda*pathSum Z h)) :=
      Finset.sum_coe_sort S (fun h => historyWeight K h*Real.exp (lambda*pathSum Z h))
    have hm : (∑ h : S, p h*Real.exp (lambda*X h)) ≤
        Real.exp ((T : ℝ)*(N*lambda^2/2+d)) := by
      rw [he]
      simpa [mul_add] using hmgf
    have h := Real.log_le_log (finite_exponential_sum_pos p (fun h => lambda*X h) hp hmass) hm
    rw [Real.log_exp] at h
    nlinarith only [h]
  have hbound := finite_chernoff_two_sided p X hp hmass ((T : ℝ)*N) ((T : ℝ)*d) u
    (mul_pos (Nat.cast_pos.mpr hT) hN) hu0 huT hlog
  have he : (∑ h : S, if u ≤ |X h| then p h else 0) =
      ∑ h ∈ S, if u ≤ |pathSum Z h| then historyWeight K h else 0 :=
    Finset.sum_coe_sort S (fun h => if u ≤ |pathSum Z h| then historyWeight K h else 0)
  rw [he] at hbound
  exact hbound

theorem killed_history_deviation_le {n : ℕ} (hn : 0 < n) (m : ℕ) (c : ℝ)
    (P : LatinRowPolicy n) (Good : LatinHistory n → Prop)
    (hcap : ∀ h, historyLive Good h → ∀ i j, P.matrix h i j ≤ c/n)
    (hm : Real.exp 2*c ≤ m) (hsize : permanentCapError m n ≤ (n : ℝ)/2)
    (g : LatinHistory n → Fin n → Fin n → ℝ) (hg : ∀ h i j, |g h i j| ≤ 1)
    (T : ℕ) (hT : 0 < T) (u : ℝ) (hu0 : 0 ≤ u) (huT : u ≤ (T : ℝ)*(2*(n : ℝ))) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) T,
      if u ≤ |pathSum (killedPermanentalStatistic P Good g) h|
      then historyWeight (P.kernel hn) h else 0) ≤
      2*Real.exp ((T : ℝ)*(2*permanentCapError m n)-u^2/(2*((T : ℝ)*(2*(n : ℝ))))) := by
  apply history_deviation_le (P.kernel hn) (killedPermanentalStatistic P Good g)
    (2*(n : ℝ)) (2*permanentCapError m n) (by positivity) ?_ T hT u hu0 huT
  intro lambda hlambda h
  have hb := killedPermanentalStatistic_mgf_le hn m c P Good hcap hm hsize g hg lambda hlambda h
  simpa only [show (2*(n : ℝ))*lambda^2/2 = (n : ℝ)*lambda^2 by ring] using hb

end LatinonEntropy

#print axioms LatinonEntropy.history_deviation_le
#print axioms LatinonEntropy.killed_history_deviation_le
