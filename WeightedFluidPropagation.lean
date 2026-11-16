module

public import ProfilePropagation
public import ProfileCutNoiseValue
public import RowEntropyBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileWeightedNoise {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (w : Fin n → Fin n → ℝ) (h : LatinHistory n)
    (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, ∑ j, (propagationKernel (fun s => profileHazard P s i j) h.length T*w i j)*
    killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j

def profileWeightedDrift {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (w : Fin n → Fin n → ℝ) (h : LatinHistory n)
    (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, ∑ j, (propagationKernel (fun s => profileHazard P s i j) h.length T*w i j)*
    killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j

theorem profile_weighted_gap_decomposition {n : ℕ} (P : PositiveLatinProfile n)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (w : Fin n → Fin n → ℝ)
    (h : LatinHistory n) (hv : LatinHistoryValid h) :
    (∑ i, ∑ j, (profileRemaining P h.length i j-stoppedAvailability Good (profileHazard P) h i j)*w i j) =
      pathSum (profileWeightedNoise P h.length S Good w) h+
        pathSum (profileWeightedDrift P h.length S Good w) h := by
  have hcell : ∀ i j,
      (profileRemaining P h.length i j-stoppedAvailability Good (profileHazard P) h i j)*w i j =
        pathSum (fun g sigma =>
          (propagationKernel (fun s => profileHazard P s i j) g.length h.length*w i j)*
            profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by
    intro i j
    have hp := profile_cell_propagation P Good (fun g => permanentMarginal (S.matrix g)) h hv i j
    change stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j = _ at hp
    have hf : (fun g sigma => (propagationKernel (fun s => profileHazard P s i j) g.length h.length*w i j)*
        profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) =
        (fun g sigma => w i j*(propagationKernel (fun s => profileHazard P s i j) g.length h.length*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j)) := by
      funext g sigma; ring
    rw [hf,pathSum_mul]
    calc
      _ = -((stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j)*w i j) := by ring
      _ = _ := by rw [hp]; ring
  calc
    _ = ∑ i, ∑ j, pathSum (fun g sigma =>
        (propagationKernel (fun s => profileHazard P s i j) g.length h.length*w i j)*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by simp_rw [hcell]
    _ = pathSum (fun g sigma => ∑ i, ∑ j,
        (propagationKernel (fun s => profileHazard P s i j) g.length h.length*w i j)*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by
      rw [pathSum_sum]; apply sum_congr rfl; intro i _; rw [pathSum_sum]
    _ = pathSum (fun g sigma => profileWeightedNoise P h.length S Good w g sigma+
        profileWeightedDrift P h.length S Good w g sigma) h := by
      apply pathSum_congr
      intro g sigma
      simp only [profileWeightedNoise,profileWeightedDrift,profileCellError,mul_add,sum_add_distrib]
    _ = _ := pathSum_add _ _ _

theorem profile_weighted_noise_mean_zero {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (w : Fin n → Fin n → ℝ) :
    historyExpectation (S.kernel P.npos) T (pathSum (profileWeightedNoise P T S Good w)) = 0 := by
  let g := fun (h : LatinHistory n) (i j : Fin n) =>
    propagationKernel (fun s => profileHazard P s i j) h.length T*w i j
  have he : profileWeightedNoise P T S Good w = killedPermanentalStatistic S Good g := by
    funext h sigma
    rw [← killed_noise_matrix_pairing]
    unfold profileWeightedNoise matrixPairing g
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  rw [he]
  exact killed_history_mean_zero P.npos S Good g T

theorem profile_weighted_drift_increment_bound {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (w : Fin n → Fin n → ℝ)
    (W : ℝ) (hw : ∀ i j, |w i j| ≤ W) (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) :
    |profileWeightedDrift P T S Good w h sigma| ≤ W*profileTotalCost P S Good h := by
  let e := fun i j => killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j
  let g := fun i j => propagationKernel (fun s => profileHazard P s i j) h.length T*w i j
  have hg : ∀ i j, |g i j| ≤ W := by
    intro i j
    have hk := propagationKernel_bounds (fun s => profileHazard P s i j) (fun s => P.hazard_mem_unit s i j) h.length T
    dsimp [g]
    rw [abs_mul,abs_of_nonneg hk.1]
    simpa only [one_mul] using mul_le_mul hk.2 (hw i j) (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
  have hb := abs_matrix_pairing_le_l1 e g W hg
  have he : (∑ i, ∑ j, e i j*g i j) = profileWeightedDrift P T S Good w h sigma := by
    unfold profileWeightedDrift e g
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  rw [he] at hb
  exact hb

theorem profile_weighted_drift_path_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (w : Fin n → Fin n → ℝ)
    (W : ℝ) (hw : ∀ i j, |w i j| ≤ W) (h : LatinHistory n) :
    |pathSum (profileWeightedDrift P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) w) h| ≤
      W*pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
  apply pathSum_abs_le_budget
  intro g sigma
  have hb := profile_weighted_drift_increment_bound P T (profileProcessPolicy P eps heps budget)
    (profileProcessGood P eps heps budget) w W hw g sigma
  rw [profileTotalCost_actual] at hb
  exact hb

end LatinonEntropy

#print axioms LatinonEntropy.profile_weighted_gap_decomposition
#print axioms LatinonEntropy.profile_weighted_noise_mean_zero
#print axioms LatinonEntropy.profile_weighted_drift_path_bound
