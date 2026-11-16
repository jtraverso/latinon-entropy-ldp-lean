module

public import ProfileCoordinateNoise
public import ProfileProcess
public import HistoryAbsoluteBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileRowNoise {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (i : Fin n) (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ j, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j*
    profileResponseWeight P T h.length i j

def profileColNoise {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (j : Fin n) (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) h sigma i j*
    profileResponseWeight P T h.length i j

def profileRowDrift {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (i : Fin n) (h : LatinHistory n) (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ j, killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j*
    profileResponseWeight P T h.length i j

def profileColDrift {n : ℕ} (P : PositiveLatinProfile n) (T : ℕ) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (j : Fin n) (h : LatinHistory n) (_sigma : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j*
    profileResponseWeight P T h.length i j

def profileRowCost {n : ℕ} (P : PositiveLatinProfile n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (i : Fin n) (h : LatinHistory n) : ℝ :=
  ∑ j, |killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j|

def profileColCost {n : ℕ} (P : PositiveLatinProfile n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (j : Fin n) (h : LatinHistory n) : ℝ :=
  ∑ i, |killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j|

def profileTotalCost {n : ℕ} (P : PositiveLatinProfile n) (S : LatinRowPolicy n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) : ℝ :=
  ∑ i, ∑ j, |killedRowDrift Good (profileHazard P) (fun g => permanentMarginal (S.matrix g)) h i j|

theorem profile_row_drift_path_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (i : Fin n) (h : LatinHistory n) :
    |pathSum (profileRowDrift P T S Good i) h| ≤ ((P.b/(P.a*eps))/n)*
      pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i g) h := by
  apply pathSum_abs_le_budget
  intro g sigma
  exact abs_weighted_sum_le univ _ _ _ (fun j _ => profileResponseWeight_bounds P eps heps T hdegree g.length i j)

theorem profile_col_drift_path_bound {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (j : Fin n) (h : LatinHistory n) :
    |pathSum (profileColDrift P T S Good j) h| ≤ ((P.b/(P.a*eps))/n)*
      pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j g) h := by
  apply pathSum_abs_le_budget
  intro g sigma
  exact abs_weighted_sum_le univ _ _ _ (fun i _ => profileResponseWeight_bounds P eps heps T hdegree g.length i j)

theorem profile_row_margin_pointwise {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (i : Fin n)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (hlen : h.length = T) :
    |(∑ j, stoppedAvailability Good (profileHazard P) h i j*profileHazard P T i j)-1| ≤
      |pathSum (profileRowNoise P T S Good i) h|+((P.b/(P.a*eps))/n)*
        pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i g) h := by
  have ht : h.length < n := by rw [hlen]; exact P.main_index eps heps T hdegree
  have hp := profile_row_propagation P Good (fun g => permanentMarginal (S.matrix g)) h hv ht i
  rw [hlen] at hp
  have he : (fun g sigma => ∑ j, profileResponseWeight P T g.length i j*
      profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) =
      (fun g sigma => profileRowNoise P T S Good i g sigma+profileRowDrift P T S Good i g sigma) := by
    funext g sigma
    simp only [profileRowNoise,profileRowDrift,profileCellError,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hp,he,pathSum_add,abs_neg]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (profile_row_drift_path_bound P eps heps T hdegree S Good i h))

theorem profile_col_margin_pointwise {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (j : Fin n)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (hlen : h.length = T) :
    |(∑ i, stoppedAvailability Good (profileHazard P) h i j*profileHazard P T i j)-1| ≤
      |pathSum (profileColNoise P T S Good j) h|+((P.b/(P.a*eps))/n)*
        pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j g) h := by
  have ht : h.length < n := by rw [hlen]; exact P.main_index eps heps T hdegree
  have hp := profile_col_propagation P Good (fun g => permanentMarginal (S.matrix g)) h hv ht j
  rw [hlen] at hp
  have he : (fun g sigma => ∑ i, profileResponseWeight P T g.length i j*
      profileCellError P Good (fun g => permanentMarginal (S.matrix g)) g sigma i j) =
      (fun g sigma => profileColNoise P T S Good j g sigma+profileColDrift P T S Good j g sigma) := by
    funext g sigma
    simp only [profileColNoise,profileColDrift,profileCellError,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hp,he,pathSum_add,abs_neg]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (profile_col_drift_path_bound P eps heps T hdegree S Good j h))

theorem expected_profile_row_margin {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (i : Fin n) :
    historyExpectation (S.kernel P.npos) T (fun h => |(∑ j, profileAuxiliaryCandidate P Good h i j)-1|) ≤
      Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2)+((P.b/(P.a*eps))/n)*
        historyExpectation (S.kernel P.npos) T
          (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i g)) := by
  have hTn := P.main_index eps heps T hdegree
  calc
    _ ≤ historyExpectation (S.kernel P.npos) T (fun h =>
        |pathSum (profileRowNoise P T S Good i) h|+((P.b/(P.a*eps))/n)*
          pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i g) h) := by
      apply historyExpectation_mono_positive
      intro h hh hpos
      have hlen := histories_length hh
      have hv := S.positive_history_valid P.npos T hTn.le h hh hpos
      change |(∑ j, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1| ≤ _
      rw [hlen]
      exact profile_row_margin_pointwise P eps heps T hdegree S Good i h hv hlen
    _ = historyExpectation (S.kernel P.npos) T (fun h => |pathSum (profileRowNoise P T S Good i) h|)+
        ((P.b/(P.a*eps))/n)*historyExpectation (S.kernel P.npos) T
          (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileRowCost P S Good i g)) := by
      rw [historyExpectation_add,historyExpectation_mul]
    _ ≤ _ := add_le_add (profile_row_noise_abs_le P eps heps T hdegree S Good i) le_rfl

theorem expected_profile_col_margin {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (j : Fin n) :
    historyExpectation (S.kernel P.npos) T (fun h => |(∑ i, profileAuxiliaryCandidate P Good h i j)-1|) ≤
      Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2)+((P.b/(P.a*eps))/n)*
        historyExpectation (S.kernel P.npos) T
          (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j g)) := by
  have hTn := P.main_index eps heps T hdegree
  calc
    _ ≤ historyExpectation (S.kernel P.npos) T (fun h =>
        |pathSum (profileColNoise P T S Good j) h|+((P.b/(P.a*eps))/n)*
          pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j g) h) := by
      apply historyExpectation_mono_positive
      intro h hh hpos
      have hlen := histories_length hh
      have hv := S.positive_history_valid P.npos T hTn.le h hh hpos
      change |(∑ i, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1| ≤ _
      rw [hlen]
      exact profile_col_margin_pointwise P eps heps T hdegree S Good j h hv hlen
    _ = historyExpectation (S.kernel P.npos) T (fun h => |pathSum (profileColNoise P T S Good j) h|)+
        ((P.b/(P.a*eps))/n)*historyExpectation (S.kernel P.npos) T
          (pathSum (fun g (_ : Equiv.Perm (Fin n)) => profileColCost P S Good j g)) := by
      rw [historyExpectation_add,historyExpectation_mul]
    _ ≤ _ := add_le_add (profile_col_noise_abs_le P eps heps T hdegree S Good j) le_rfl

end LatinonEntropy

#print axioms LatinonEntropy.expected_profile_row_margin
#print axioms LatinonEntropy.expected_profile_col_margin
