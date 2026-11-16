module

public import WeightedFluidPropagation
public import EntropyWeights
public import ProfileDefectStability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

/-- The expected weighted fluid gap is paid by actual stopped drift.
Noise is centered at the actual conditional marginal and cancels exactly. -/
theorem profile_weighted_gap_expectation_le {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (hT : T ≤ n)
    (w : Fin n → Fin n → ℝ) (W : ℝ) (hw : ∀ i j, |w i j| ≤ W) :
    historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
      (fun h => ∑ i, ∑ j, (profileRemaining P T i j-
        stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h i j)*w i j) ≤
      W*historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
        (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g)) := by
  let S := profileProcessPolicy P eps heps budget
  let Good := profileProcessGood P eps heps budget
  let K := S.kernel P.npos
  have he := historyExpectation_congr_positive K T
    (fun h => ∑ i, ∑ j, (profileRemaining P T i j-stoppedAvailability Good (profileHazard P) h i j)*w i j)
    (fun h => pathSum (profileWeightedNoise P T S Good w) h+pathSum (profileWeightedDrift P T S Good w) h)
    (fun h hh hp => by
      have hv := S.positive_history_valid P.npos T hT h hh hp
      have hd := profile_weighted_gap_decomposition P S Good w h hv
      rw [histories_length hh] at hd
      exact hd)
  have hnoise := profile_weighted_noise_mean_zero P T S Good w
  rw [historyExpectation_add,hnoise,zero_add] at he
  have hd : historyExpectation K T (pathSum (profileWeightedDrift P T S Good w)) ≤
      W*historyExpectation K T
        (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g)) := by
    calc
      _ ≤ historyExpectation K T (fun h => W*pathSum
          (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h) := by
        apply historyExpectation_mono
        intro h _
        exact (le_abs_self _).trans (profile_weighted_drift_path_bound P eps heps budget T w W hw h)
      _ = _ := historyExpectation_mul K T W _
  exact he.le.trans hd

/-- An actual expectation bound for the auxiliary entropy statistic.
The budget and its Gronwall estimate are derived from the constructed law. -/
theorem profile_aux_entropy_expectation_lower {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (m : ℕ) (hm : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) :
    profileFluidRowEntropy P T-profileEntropyWeightCap P eps*((T : ℝ)*
      (Real.sqrt (2*(n : ℝ)*permanentCapError m n)+3*profileStabilityBound P eps m)) ≤
      historyExpectation ((profileProcessPolicy P eps heps budget).kernel P.npos) T
        (fun h => profileLinearEntropy P T
          (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h)) := by
  let K := (profileProcessPolicy P eps heps budget).kernel P.npos
  let B := fun h => profileLinearEntropy P T
    (stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h)
  have hw : ∀ i j, |profileEntropyWeight P T i j| ≤ profileEntropyWeightCap P eps := by
    intro i j
    rw [abs_of_nonneg (profileEntropyWeight_nonneg P T i j)]
    exact profileEntropyWeight_le_cap P eps heps T hdegree i j
  have hgap := profile_weighted_gap_expectation_le P eps heps budget T
    (P.main_index eps heps T hdegree).le (profileEntropyWeight P T) (profileEntropyWeightCap P eps) hw
  have he : (fun h : LatinHistory n => ∑ i, ∑ j, (profileRemaining P T i j-
      stoppedAvailability (profileProcessGood P eps heps budget) (profileHazard P) h i j)*profileEntropyWeight P T i j) =
      (fun h => profileFluidRowEntropy P T-B h) := by
    funext h
    dsimp only [B,profileFluidRowEntropy,profileLinearEntropy]
    simp only [sub_mul,sum_sub_distrib]
  rw [he] at hgap
  have hc : historyExpectation K T (fun h => profileFluidRowEntropy P T-B h) =
      profileFluidRowEntropy P T-historyExpectation K T B := by
    have hfun : (fun h : LatinHistory n => profileFluidRowEntropy P T-B h) =
        (fun h => profileFluidRowEntropy P T+(-1)*B h) := by funext h; ring
    rw [hfun,historyExpectation_add,historyExpectation_const,historyExpectation_mul]
    ring
  rw [hc] at hgap
  have hbudget := mul_le_mul_of_nonneg_left (expected_profile_budget_uniform P eps heps budget m hm hsize T hdegree)
    (profileEntropyWeightCap_nonneg P eps heps)
  linarith only [hgap,hbudget]

end LatinonEntropy

#print axioms LatinonEntropy.profile_weighted_gap_expectation_le
#print axioms LatinonEntropy.profile_aux_entropy_expectation_lower
