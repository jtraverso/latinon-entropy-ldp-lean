module

public import ProfileMonitorTests
public import ProfileExpectedRecurrence

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def profileMonitorNoise {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (I U V : Finset (Fin n)) (h : LatinHistory n)
    (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, profileMonitorWeight P T I h.length i j*
    killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j

def profileMonitorDrift {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (I U V : Finset (Fin n)) (h : LatinHistory n)
    (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, profileMonitorWeight P T I h.length i j*
    killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j

theorem pathSum_div {Ω : Type*} (X : List Ω → Ω → ℝ) (c : ℝ) (h : List Ω) :
    pathSum (fun g a => X g a/c) h = pathSum X h/c := by
  calc
    _ = pathSum (fun g a => (1/c)*X g a) h := pathSum_congr _ _ (fun _ _ => by ring) h
    _ = (1/c)*pathSum X h := pathSum_mul _ _ _
    _ = _ := by ring

theorem profile_monitor_noise_value {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (I U V : Finset (Fin n))
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (ht : h.length < T) :
    killedPermanentalStatistic S Good (profileMonitorTest P T I U V) h sigma =
      profileMonitorNoise P T S Good I U V h sigma/2 := by
  rw [← killed_noise_matrix_pairing]
  have he : profileMonitorTest P T I U V h = (fun i j =>
      if i ∈ U ∧ j ∈ V then profileMonitorWeight P T I h.length i j/2 else 0) := by
    funext i j; simp only [profileMonitorTest,ht,true_and]
  rw [he,matrixPairing_cut_mask]
  simp only [profileMonitorNoise,sum_div]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem profile_monitor_noise_zero_after {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (I U V : Finset (Fin n))
    (h : LatinHistory n) (ht : T ≤ h.length) (sigma : Equiv.Perm (Fin n)) :
    killedPermanentalStatistic S Good (profileMonitorTest P T I U V) h sigma = 0 := by
  simp [killedPermanentalStatistic,profileMonitorTest,not_lt.mpr ht,permutationStatistic,matrixPairing]

theorem profile_monitor_noise_prefix_identity {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (I U V : Finset (Fin n))
    (h : LatinHistory n) (ht : T ≤ h.length) :
    pathSum (killedPermanentalStatistic S Good (profileMonitorTest P T I U V)) h =
      pathSum (profileMonitorNoise P T S Good I U V) (historyPrefix h T)/2 := by
  rw [pathSum_local_to_prefix _ T (fun g hg sigma => profile_monitor_noise_zero_after P T S Good I U V g hg sigma) h ht]
  calc
    _ = pathSum (fun g sigma => profileMonitorNoise P T S Good I U V g sigma/2) (historyPrefix h T) :=
      pathSum_congr_before _ _ T (fun g hg sigma => profile_monitor_noise_value P T S Good I U V g sigma hg)
        (historyPrefix h T) (historyPrefix_length h T ht).le
    _ = _ := pathSum_div _ 2 _

theorem abs_signed_rectangle_pairing_le_two {n : ℕ} (e w : Fin n → Fin n → ℝ)
    (U V : Finset (Fin n)) (hw : ∀ i j, |w i j| ≤ 2) :
    |∑ i ∈ U, ∑ j ∈ V, w i j*e i j| ≤ 2*(∑ i, ∑ j, |e i j|) := by
  have hsum : (∑ i ∈ U, ∑ j ∈ V, |e i j|) ≤ ∑ i, ∑ j, |e i j| :=
    (sum_le_sum (fun i _ => sum_subset_le_total _ (fun j => abs_nonneg _) V)).trans
      (sum_subset_le_total _ (fun i => sum_nonneg (fun j _ => abs_nonneg _)) U)
  calc
    _ ≤ ∑ i ∈ U, |∑ j ∈ V, w i j*e i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ U, ∑ j ∈ V, 2*|e i j| := by
      apply sum_le_sum
      intro i _
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hw i j) (abs_nonneg _)))
    _ = 2*(∑ i ∈ U, ∑ j ∈ V, |e i j|) := by simp only [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

theorem profile_monitor_drift_path_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (budget : ℝ) (T : ℕ) (I U V : Finset (Fin n)) (h : LatinHistory n) :
    |pathSum (profileMonitorDrift P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) I U V) h| ≤
      2*pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileActualDriftCost P eps heps budget g) h := by
  apply pathSum_abs_le_budget
  intro g sigma
  have hb := abs_signed_rectangle_pairing_le_two
    (fun i j => killedRowDrift (profileProcessGood P eps heps budget) (profileHazard P)
      (fun g => permanentMarginal ((profileProcessPolicy P eps heps budget).matrix g)) g i j)
    (profileMonitorWeight P T I g.length) U V (profileMonitorWeight_abs_le P T I g.length)
  change |profileMonitorDrift P T (profileProcessPolicy P eps heps budget)
      (profileProcessGood P eps heps budget) I U V g sigma| ≤
    2*profileTotalCost P (profileProcessPolicy P eps heps budget) (profileProcessGood P eps heps budget) g at hb
  rw [profileTotalCost_actual] at hb
  exact hb

end LatinonEntropy

#print axioms LatinonEntropy.profile_monitor_noise_prefix_identity
#print axioms LatinonEntropy.profile_monitor_drift_path_bound
