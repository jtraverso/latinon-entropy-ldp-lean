module

public import ProfileExpectedRecurrence

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileCutNoiseIncrement {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, propagationKernel (fun s => profileHazard P s i j) h.length t*
    killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j

def profileCutDriftIncrement {n : ℕ} (P : PositiveLatinProfile n) (t : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, propagationKernel (fun s => profileHazard P s i j) h.length t*
    killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j

theorem profile_cut_defect_decomposition {n : ℕ} (P : PositiveLatinProfile n)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (hv : LatinHistoryValid h) :
    rectMass (profileRemaining P h.length) U V-
        rectMass (stoppedAvailability Good (profileHazard P) h) U V =
      pathSum (profileCutNoiseIncrement P h.length S Good U V) h+
        pathSum (profileCutDriftIncrement P h.length S Good U V) h := by
  have hp : rectMass (profileCellDefect P Good h) U V =
      -pathSum (fun g sigma => ∑ i ∈ U, ∑ j ∈ V,
        propagationKernel (fun s => profileHazard P s i j) g.length h.length*
          profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) h := by
    unfold rectMass
    simp_rw [profile_cell_propagation P Good (fun g => permanentMarginal (S.matrix g)) h hv]
    simp only [sum_neg_distrib]
    congr 1
    rw [pathSum_sum]
    apply sum_congr rfl
    intro i _
    rw [pathSum_sum]
  have he : (fun g sigma => ∑ i ∈ U, ∑ j ∈ V,
      propagationKernel (fun s => profileHazard P s i j) g.length h.length*
        profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) =
      (fun g sigma => profileCutNoiseIncrement P h.length S Good U V g sigma+
        profileCutDriftIncrement P h.length S Good U V g sigma) := by
    funext g sigma
    simp only [profileCutNoiseIncrement,profileCutDriftIncrement,profileCellError,mul_add,sum_add_distrib]
  rw [he,pathSum_add] at hp
  simp only [rectMass,profileCellDefect,sum_sub_distrib] at hp ⊢
  linarith only [hp]

theorem profile_cut_drift_increment_bound {n : ℕ} (P : PositiveLatinProfile n)
    (t : ℕ) (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (U V : Finset (Fin n))
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) :
    |profileCutDriftIncrement P t S Good U V h sigma| ≤ profileTotalCost P S Good h := by
  let e := fun i j => killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j
  have hk : ∀ i j, 0 ≤ propagationKernel (fun s => profileHazard P s i j) h.length t ∧
      propagationKernel (fun s => profileHazard P s i j) h.length t ≤ 1 :=
    fun i j => propagationKernel_bounds _ (fun s => P.hazard_mem_unit s i j) _ _
  calc
    _ ≤ ∑ i ∈ U, |∑ j ∈ V, propagationKernel (fun s => profileHazard P s i j) h.length t*e i j| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ U, ∑ j ∈ V, |e i j| := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j ∈ V, |propagationKernel (fun s => profileHazard P s i j) h.length t*e i j| :=
          abs_sum_le_sum_abs _ _
        _ ≤ _ := sum_le_sum (fun j _ => by
          rw [abs_mul,abs_of_nonneg (hk i j).1]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hk i j).2 (abs_nonneg (e i j)))
    _ ≤ ∑ i ∈ U, ∑ j, |e i j| := sum_le_sum (fun i _ => sum_subset_le_total _ (fun j => abs_nonneg _) V)
    _ ≤ _ := sum_subset_le_total _ (fun i => sum_nonneg (fun j _ => abs_nonneg _)) U

theorem profile_cut_drift_path_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (t : ℕ) (U V : Finset (Fin n)) (h : LatinHistory n) :
    |pathSum (profileCutDriftIncrement P t (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) U V) h| ≤
      pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
  have hb := pathSum_abs_le_budget
    (profileCutDriftIncrement P t (profileProcessPolicy P eps heps budget) (profileProcessGood P eps heps budget) U V)
    (profileActualDriftCost P eps heps budget) 1 (fun g sigma => by
      simpa only [one_mul,profileTotalCost_actual] using
        profile_cut_drift_increment_bound P t (profileProcessPolicy P eps heps budget)
          (profileProcessGood P eps heps budget) U V g sigma) h
  simpa only [one_mul] using hb

end LatinonEntropy

#print axioms LatinonEntropy.profile_cut_defect_decomposition
#print axioms LatinonEntropy.profile_cut_drift_path_bound
