module

public import HistoryEventBounds
public import HistoryPrefixes
public import UniformProfileSurvival

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem historyExpectation_prefix {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (F : List Ω → ℝ) (T N : ℕ) (hTN : T ≤ N) :
    historyExpectation K N (fun h => F (historyPrefix h T)) = historyExpectation K T F := by
  induction N generalizing T with
  | zero => have he : T = 0 := by omega
            simp [he,historyExpectation,histories,historyWeight,historyPrefix]
  | succ N ih =>
    by_cases hT : T ≤ N
    · rw [historyExpectation_tower]
      calc
        _ = historyExpectation K N (fun h => F (historyPrefix h T)) := by
          apply historyExpectation_congr_positive
          intro h hh _
          have hlen : T ≤ h.length := by rw [histories_length hh]; exact hT
          have he : ∀ a : Ω, historyPrefix (a::h) T = historyPrefix h T := fun a => historyPrefix_cons a h T hlen
          simp_rw [he]
          rw [← sum_mul,K.total,one_mul]
        _ = _ := ih T hT
    · have he : T = N+1 := by omega
      subst T
      apply historyExpectation_congr_positive
      intro h hh _
      rw [← histories_length hh,historyPrefix_self]

theorem historyEventMass_eq_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (N : ℕ) (E : List Ω → Prop) :
    historyEventMass K N E = historyExpectation K N (fun h => if E h then (1 : ℝ) else 0) := by
  unfold historyEventMass historyExpectation
  apply sum_congr rfl
  intro h _
  by_cases he : E h
  · simp only [he,ite_true,mul_one]
  · simp only [he,ite_false,mul_zero]

theorem history_event_mass_prefix {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (E : List Ω → Prop) (T N : ℕ) (hTN : T ≤ N) :
    historyEventMass K N (fun h => E (historyPrefix h T)) = historyEventMass K T E := by
  rw [historyEventMass_eq_expectation,historyEventMass_eq_expectation]
  exact historyExpectation_prefix K (fun h => if E h then (1 : ℝ) else 0) T N hTN

theorem history_notLive_mass_step {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (Good : List Ω → Prop) (T : ℕ) :
    historyEventMass K (T+1) (fun h => ¬historyPastLive Good h) =
      historyEventMass K T (fun h => ¬historyLive Good h) := by
  unfold historyEventMass
  rw [history_sum_succ]
  apply sum_congr rfl
  intro h _
  by_cases hl : historyLive Good h
  · simp only [historyPastLive,hl,not_true_eq_false,ite_false,sum_const_zero]
  · simp only [historyPastLive,hl,not_false_eq_true,ite_true,historyWeight,← mul_sum,K.total,mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- A row-level stopped mass is compared to the SAME full-history law by
proved prefix consistency, then bounded by the certified finite survival rate. -/
theorem profile_notLive_mass_le_rate {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (t : ℕ) (ht : t < T) :
    historyEventMass ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) t
      (fun h => ¬historyLive (profileProcessGood P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)) h) ≤
      profileSurvivalRate a b eps m n := by
  let v := fixedCutDensity a b eps*(n : ℝ)^2/4
  let K := (profileProcessPolicy P eps heps v).kernel P.npos
  let Good := profileProcessGood P eps heps v
  have htT : t+1 ≤ T := ht
  have htN : t+1 ≤ n := htT.trans (P.main_index eps heps T hdegree).le
  have htR : ((t+1 : ℕ) : ℝ) ≤ T := Nat.cast_le.mpr htT
  have hdeg : eps*n ≤ (n : ℝ)-(t+1 : ℕ) := by linarith only [hdegree,htR]
  have hr := profile_survival_rate_bound P a b eps heps ha hb m hm hsize (t+1) hdeg
  have hbound : historyEventMass K n (fun h => ¬historyPastLive Good (historyPrefix h (t+1))) ≤
      profileSurvivalRate a b eps m n := by
    simpa only [K,Good,v,historyEventMass,history_event_indicator_canonical] using hr
  rw [history_event_mass_prefix K (fun h => ¬historyPastLive Good h) (t+1) n htN,
    history_notLive_mass_step] at hbound
  exact hbound

end LatinonEntropy

#print axioms LatinonEntropy.history_event_mass_prefix
#print axioms LatinonEntropy.profile_notLive_mass_le_rate
