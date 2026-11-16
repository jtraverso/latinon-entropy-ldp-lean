module

public import ProfileExpectedRecurrence

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileStabilityBound {n : ℕ} (P : PositiveLatinProfile n) (eps : ℝ) (m : ℕ) : ℝ :=
  (2*(P.b/(P.a*eps))*Real.sqrt (n : ℝ)+
    2*(P.b/(P.a*eps))*Real.sqrt (2*(n : ℝ)*permanentCapError m n))*Real.exp (6*(P.b/(P.a*eps)))

theorem profileExpectedDefect_nonneg {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) :
    0 ≤ profileExpectedDefect P eps heps budget T :=
  historyExpectation_nonneg _ _ _ (fun _ _ => matrixMarginDefect_nonneg _)

theorem profile_expected_defect_finite_gronwall {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (Tmax : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-Tmax) (t : ℕ) (ht : t ≤ Tmax) :
    profileExpectedDefect P eps heps budget t ≤
      (2*(P.b/(P.a*eps))*Real.sqrt (n : ℝ)+
        (t : ℝ)*(2*(P.b/(P.a*eps))/n)*Real.sqrt (2*(n : ℝ)*permanentCapError m n))*
      Real.exp ((t : ℝ)*(2*(P.b/(P.a*eps))/n)*3) := by
  let c : ℝ := P.b/(P.a*eps)
  have hc : 0 ≤ c := div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le
  apply finite_defect_gronwall (profileExpectedDefect P eps heps budget)
    (2*c*Real.sqrt (n : ℝ)) (2*c/n) (Real.sqrt (2*(n : ℝ)*permanentCapError m n)) 3 Tmax
    (by positivity) (by positivity) (Real.sqrt_nonneg _) (by norm_num)
    (profileExpectedDefect_nonneg P eps heps budget) ?_ t ht
  intro s hs
  have hsR : (s : ℝ) ≤ Tmax := Nat.cast_le.mpr hs
  have hdeg : eps*n ≤ (n : ℝ)-s := by linarith only [hdegree,hsR]
  exact profile_expected_defect_recurrence P eps heps budget m hm hsize s hdeg

theorem profile_expected_defect_uniform {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (Tmax : ℕ)
    (hdegree : eps*n ≤ (n : ℝ)-Tmax) (t : ℕ) (ht : t ≤ Tmax) :
    profileExpectedDefect P eps heps budget t ≤ profileStabilityBound P eps m := by
  let c : ℝ := P.b/(P.a*eps)
  let B : ℝ := Real.sqrt (2*(n : ℝ)*permanentCapError m n)
  let A : ℝ := 2*c*Real.sqrt (n : ℝ)
  have hc : 0 ≤ c := div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) hc) (Real.sqrt_nonneg _)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have htR : (t : ℝ) ≤ n := Nat.cast_le.mpr (ht.trans (P.main_index eps heps Tmax hdegree).le)
  have hb : 0 ≤ 2*c/n := div_nonneg (mul_nonneg (by norm_num) hc) hnR.le
  have hscale : (t : ℝ)*(2*c/n) ≤ 2*c := by
    calc
      _ ≤ (n : ℝ)*(2*c/n) := mul_le_mul_of_nonneg_right htR hb
      _ = _ := by field_simp
  have hcoeff : A+(t : ℝ)*(2*c/n)*B ≤ A+2*c*B :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right hscale hB)
  have hexp : (t : ℝ)*(2*c/n)*3 ≤ 6*c := by nlinarith only [hscale]
  have hbase := profile_expected_defect_finite_gronwall P eps heps budget m hm hsize Tmax hdegree t ht
  change profileExpectedDefect P eps heps budget t ≤ (A+2*c*B)*Real.exp (6*c)
  calc
    _ ≤ (A+(t : ℝ)*(2*c/n)*B)*Real.exp ((t : ℝ)*(2*c/n)*3) := hbase
    _ ≤ (A+2*c*B)*Real.exp ((t : ℝ)*(2*c/n)*3) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
      (add_nonneg hA (mul_nonneg (mul_nonneg (by norm_num) hc) hB))

theorem expected_profile_budget_uniform {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
      (pathSum (fun h (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget h)) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m) := by
  have hsum : (∑ s ∈ range T, profileExpectedDefect P eps heps budget s) ≤
      (T : ℝ)*profileStabilityBound P eps m := by
    calc
      _ ≤ ∑ _s ∈ range T, profileStabilityBound P eps m := sum_le_sum (fun s hs =>
        profile_expected_defect_uniform P eps heps budget m hm hsize T hdegree s (le_of_lt (mem_range.mp hs)))
      _ = _ := by simp
  have h := expected_profile_budget_le P eps heps budget m hm hsize T
  nlinarith only [h,hsum]

theorem profile_budget_markov_uniform {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (m : ℕ)
    (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (v : ℝ) (hv : 0 < v) :
    (∑ h ∈ histories (Equiv.Perm (Fin n)) T,
      if v ≤ pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h
      then historyWeight ((profileProcessPolicy P eps heps budget).kernel P.npos) h else 0) ≤
      (T : ℝ)*(Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)/v := by
  have hnonneg : ∀ h : LatinHistory n,
      0 ≤ pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
    intro h
    induction h with
    | nil => exact le_rfl
    | cons sigma h ih => exact add_nonneg ih (profileActualDriftCost_nonneg P eps heps budget h)
  exact (history_markov ((profileProcessPolicy P eps heps budget).kernel P.npos) T _
    (fun h _ => hnonneg h) v hv).trans (div_le_div_of_nonneg_right
      (expected_profile_budget_uniform P eps heps budget m hm hsize T hdegree) hv.le)

end LatinonEntropy

#print axioms LatinonEntropy.profile_expected_defect_uniform
#print axioms LatinonEntropy.expected_profile_budget_uniform
#print axioms LatinonEntropy.profile_budget_markov_uniform
