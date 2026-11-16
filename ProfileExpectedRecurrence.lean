module

public import ProfileMarginEstimates
public import FiniteDefectGronwall

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

theorem profile_cost_sum_rows {n : ℕ} (P : PositiveLatinProfile n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (T : ℕ) :
    (∑ i, historyExpectation (S.kernel P.npos) T
      (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i h))) =
      historyExpectation (S.kernel P.npos) T
        (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P S Good h)) :=
  history_predictable_cost_sum (S.kernel P.npos) T univ (profileRowCost P S Good)

theorem profile_cost_sum_cols {n : ℕ} (P : PositiveLatinProfile n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (T : ℕ) :
    (∑ j, historyExpectation (S.kernel P.npos) T
      (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j h))) =
      historyExpectation (S.kernel P.npos) T
        (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P S Good h)) := by
  have hs := history_predictable_cost_sum (S.kernel P.npos) T univ (profileColCost P S Good)
  have he : (fun h (_ : Equiv.Perm (Fin n)) => ∑ j, profileColCost P S Good j h) =
      (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P S Good h) := by
    funext h sigma
    unfold profileColCost profileTotalCost
    rw [sum_comm]
  rw [he] at hs
  exact hs

theorem expected_profile_margin_total {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) :
    historyExpectation (S.kernel P.npos) T (fun h => matrixMarginDefect (profileAuxiliaryCandidate P Good h)) ≤
      2*(n : ℝ)*Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2)+2*((P.b/(P.a*eps))/n)*
        historyExpectation (S.kernel P.npos) T
          (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P S Good h)) := by
  let b : ℝ := (P.b/(P.a*eps))/n
  let r : ℝ := Real.sqrt ((T : ℝ)*b^2)
  let budget := historyExpectation (S.kernel P.npos) T
    (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P S Good h))
  have hr : (∑ i, historyExpectation (S.kernel P.npos) T
      (fun h => |(∑ j, profileAuxiliaryCandidate P Good h i j)-1|)) ≤ (n : ℝ)*r+b*budget := by
    calc
      _ ≤ ∑ i : Fin n, (r+b*historyExpectation (S.kernel P.npos) T
          (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i h))) :=
        sum_le_sum (fun i _ => expected_profile_row_margin P eps heps T hdegree S Good i)
      _ = (n : ℝ)*r+b*(∑ i, historyExpectation (S.kernel P.npos) T
          (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i h))) := by
        simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      _ = _ := by rw [profile_cost_sum_rows]
  have hc : (∑ j, historyExpectation (S.kernel P.npos) T
      (fun h => |(∑ i, profileAuxiliaryCandidate P Good h i j)-1|)) ≤ (n : ℝ)*r+b*budget := by
    calc
      _ ≤ ∑ j : Fin n, (r+b*historyExpectation (S.kernel P.npos) T
          (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j h))) :=
        sum_le_sum (fun j _ => expected_profile_col_margin P eps heps T hdegree S Good j)
      _ = (n : ℝ)*r+b*(∑ j, historyExpectation (S.kernel P.npos) T
          (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j h))) := by
        simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      _ = _ := by rw [profile_cost_sum_cols]
  have he : historyExpectation (S.kernel P.npos) T
      (fun h => matrixMarginDefect (profileAuxiliaryCandidate P Good h)) =
      (∑ i, historyExpectation (S.kernel P.npos) T
        (fun h => |(∑ j, profileAuxiliaryCandidate P Good h i j)-1|))+
      (∑ j, historyExpectation (S.kernel P.npos) T
        (fun h => |(∑ i, profileAuxiliaryCandidate P Good h i j)-1|)) := by
    simp only [matrixMarginDefect,historyExpectation_add,historyExpectation_sum]
  rw [he]
  have h := add_le_add hr hc
  nlinarith only [h]

theorem profileTotalCost_actual {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (h : LatinHistory n) :
    profileTotalCost P (profileProcessPolicy P eps heps budget) (profileProcessGood P eps heps budget) h =
      profileActualDriftCost P eps heps budget h := by
  by_cases hlive : historyLive (profileProcessGood P eps heps budget) h
  · simp only [profileTotalCost,killedRowDrift,profileActualDriftCost,profileCandidate,hlive,ite_true]
  · simp only [profileTotalCost,killedRowDrift,profileActualDriftCost,hlive,ite_false,abs_zero,sum_const_zero]

theorem profileExpectedDefect_preRecurrence {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    profileExpectedDefect P eps heps budget T ≤
      2*(n : ℝ)*Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2)+2*((P.b/(P.a*eps))/n)*
        ((T : ℝ)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
          3*(∑ t ∈ range T, profileExpectedDefect P eps heps budget t)) := by
  have h := expected_profile_margin_total P eps heps T hdegree
    (profileProcessPolicy P eps heps budget) (profileProcessGood P eps heps budget)
  have he : (fun h (_ : Equiv.Perm (Fin n)) => profileTotalCost P (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) h) =
      (fun h (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget h) := by
    funext h sigma
    exact profileTotalCost_actual P eps heps budget h
  rw [he] at h
  have hb : 0 ≤ 2*((P.b/(P.a*eps))/n) := mul_nonneg (by norm_num)
    (div_nonneg (div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le) (Nat.cast_nonneg n))
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (expected_profile_budget_le P eps heps budget m hm hsize T) hb))

/-- The actual expected-defect recurrence. It is derived from the concrete
profile process, positive-prefix validity, coordinate noise and C1+C2. -/
theorem profile_expected_defect_recurrence {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    profileExpectedDefect P eps heps budget T ≤ 2*(P.b/(P.a*eps))*Real.sqrt (n : ℝ)+
      (2*(P.b/(P.a*eps))/n)*(∑ t ∈ range T,
        (Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileExpectedDefect P eps heps budget t)) := by
  have hc : 0 ≤ P.b/(P.a*eps) :=
    div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le
  have hTn := (P.main_index eps heps T hdegree).le
  calc
    _ ≤ 2*(n : ℝ)*Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2)+2*((P.b/(P.a*eps))/n)*
        ((T : ℝ)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
          3*(∑ t ∈ range T, profileExpectedDefect P eps heps budget t)) :=
      profileExpectedDefect_preRecurrence P eps heps budget m hm hsize T hdegree
    _ ≤ 2*(P.b/(P.a*eps))*Real.sqrt (n : ℝ)+2*((P.b/(P.a*eps))/n)*
        ((T : ℝ)*Real.sqrt (2*(n : ℝ)*permanentCapError m n)+
          3*(∑ t ∈ range T, profileExpectedDefect P eps heps budget t)) :=
      add_le_add (total_coordinate_noise_le n T P.npos hTn _ hc) le_rfl
    _ = _ := by
      simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,← mul_sum]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.expected_profile_margin_total
#print axioms LatinonEntropy.profile_expected_defect_recurrence
