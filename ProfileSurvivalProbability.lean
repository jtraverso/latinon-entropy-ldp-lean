module

public import ProfileSurvivalEvent

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem history_event_indicator_canonical (p : Prop) (d : Decidable p) (w : ℝ) :
    @ite ℝ p d w 0 = @ite ℝ p (Classical.propDecidable p) w 0 := by
  by_cases hp : p
  · simp only [hp,ite_true]
  · simp only [hp,ite_false]

theorem history_event_split {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (N : ℕ) (E B C : List Ω → Prop)
    (hsplit : ∀ h ∈ histories Ω N, 0 < historyWeight K h → E h → B h ∨ C h) :
    (∑ h ∈ histories Ω N, if E h then historyWeight K h else 0) ≤
      (∑ h ∈ histories Ω N, if B h then historyWeight K h else 0)+
        (∑ h ∈ histories Ω N, if C h then historyWeight K h else 0) := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro h hh
  have hnn := historyWeight_nonneg K h
  by_cases hw : historyWeight K h = 0
  · simp only [hw,ite_self,add_zero,le_refl]
  · by_cases he : E h
    · have hp : 0 < historyWeight K h := lt_of_le_of_ne hnn (Ne.symm hw)
      rcases hsplit h hh hp he with hb | hc
      · simp only [he,hb,ite_true]
        have hc0 : 0 ≤ (if C h then historyWeight K h else 0) := by split_ifs; exact hnn; exact le_rfl
        linarith only [hc0]
      · simp only [he,hc,ite_true]
        have hb0 : 0 ≤ (if B h then historyWeight K h else 0) := by split_ifs; exact hnn; exact le_rfl
        linarith only [hb0]
    · simp only [he,ite_false]
      apply add_nonneg <;> split_ifs <;> first | exact hnn | exact le_rfl

theorem profileCutTolerance_pos {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) : 0 < profileCutTolerance P eps heps := by
  have hupper : 0 < (profileCorrectionParameters P eps heps).upper := by
    exact (lt_of_lt_of_le P.a_pos (le_max_left P.a (P.b/(P.a*eps)))).trans_le (le_max_left _ _)
  unfold profileCutTolerance
  exact div_pos (mul_pos (mul_pos (profileCorrectionParameters P eps heps).rho_pos heps)
    (sq_pos_of_pos (Nat.cast_pos.mpr P.npos))) (mul_pos (by norm_num) hupper)

theorem profile_cut_threshold_admissible {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    profileCutTolerance P eps heps/2 ≤ (n : ℝ)*(2*(n : ℝ)) := by
  let p := profileCorrectionParameters P eps heps
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have heps1 : eps ≤ 1 := by nlinarith only [hdegree,hn,Nat.cast_nonneg (α := ℝ) T]
  have hr : 0 < p.rho*eps := mul_pos p.rho_pos heps
  have hr1 : p.rho*eps ≤ 1 := by
    simpa only [one_mul] using mul_le_mul p.rho_le heps1 heps.le (zero_le_one : (0 : ℝ) ≤ 1)
  have hu : 16 ≤ p.upper := by
    calc
      _ ≤ 16/(p.rho*eps) := (le_div_iff₀ hr).mpr (by nlinarith only [hr1])
      _ ≤ _ := le_max_right _ _
  have hd : 0 < 64*p.upper := by linarith only [hu]
  have hb : p.rho*eps*(n : ℝ)^2/(64*p.upper) ≤ (n : ℝ)^2 :=
    (div_le_iff₀ hd).mpr (by
      have hmul := mul_le_mul_of_nonneg_right hr1 (sq_nonneg (n : ℝ))
      have humul := mul_le_mul_of_nonneg_right hu (sq_nonneg (n : ℝ))
      nlinarith only [hmul,humul,sq_nonneg (n : ℝ)])
  change (p.rho*eps*(n : ℝ)^2/(64*p.upper))/2 ≤ _
  nlinarith only [hb,sq_nonneg (n : ℝ)]

/-- Premature stopping bound on the full n-row probability law. The
intentional switch to fallback in the tail is outside this bad event. -/
theorem profile_main_survival_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (v : ℝ) (hv : 0 < v) (T : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-T) (hvsmall : v ≤ profileCutTolerance P eps heps/2)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) n,
      if ¬historyPastLive (profileProcessGood P eps heps v) (historyPrefix h T)
      then historyWeight ((profileProcessPolicy P eps heps v).kernel P.npos) h else 0) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v+
        ((T : ℝ)*((2 : ℝ)^n)^2)*
          (2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-
            (profileCutTolerance P eps heps/2)^2/(2*((n : ℝ)*(2*(n : ℝ)))))) := by
  have hTn : T ≤ n := (P.main_index eps heps T hdegree).le
  have hu : 0 ≤ profileCutTolerance P eps heps/2 := (half_pos (profileCutTolerance_pos P eps heps)).le
  have hthreshold := profile_cut_threshold_admissible P eps heps T hdegree
  have hsplit : ∀ h ∈ histories (Equiv.Perm (Fin n)) n,
      0 < historyWeight ((profileProcessPolicy P eps heps v).kernel P.npos) h →
      (¬historyPastLive (profileProcessGood P eps heps v) (historyPrefix h T)) →
      v ≤ profileMainBudget P eps heps v T h ∨
        ∃ t : Fin T, ∃ U V : Finset (Fin n), profileCutTolerance P eps heps/2 ≤
          |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps v)
            (profileProcessGood P eps heps v) (profileCutTest P t.val U V)) h| := by
    intro h hh hpos hbad
    have hvalid := (profileProcessPolicy P eps heps v).positive_history_valid P.npos n le_rfl h hh hpos
    exact profile_main_failure_inclusion P eps heps v T hdegree hvsmall h hvalid
      (by rw [histories_length hh]; exact hTn) hbad
  have hs := history_event_split ((profileProcessPolicy P eps heps v).kernel P.npos) n
    (fun h => ¬historyPastLive (profileProcessGood P eps heps v) (historyPrefix h T))
    (fun h => v ≤ profileMainBudget P eps heps v T h)
    (fun h => ∃ t : Fin T, ∃ U V : Finset (Fin n), profileCutTolerance P eps heps/2 ≤
      |pathSum (killedPermanentalStatistic (profileProcessPolicy P eps heps v)
        (profileProcessGood P eps heps v) (profileCutTest P t.val U V)) h|) hsplit
  have hbound := add_le_add
    (profile_full_history_budget_markov P eps heps v m hm hsize T n hTn hdegree v hv)
    (profile_simultaneous_cut_noise P eps heps v m hm hsize T (profileCutTolerance P eps heps/2) hu hthreshold)
  simp only [profileMainBudget,history_event_indicator_canonical] at hs hbound ⊢
  exact hs.trans hbound

end LatinonEntropy

#print axioms LatinonEntropy.profile_main_survival_bound
