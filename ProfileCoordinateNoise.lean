module

public import ProfilePropagation
public import PermanentCoordinateValues

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

theorem profile_row_noise_abs_le {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (i : Fin n) :
    historyExpectation (S.kernel P.npos) T (fun h => |pathSum (fun g sigma =>
      ∑ j, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*
        profileResponseWeight P T g.length i j) h|) ≤
      Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2) := by
  let w : LatinHistory n → Fin n → ℝ := fun g j => profileResponseWeight P T g.length i j
  have he : (fun g sigma => ∑ j,
      killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*w g j) =
      killedCenteredValue (S.kernel P.npos) Good (fun g tau => w g (tau i)) := by
    funext g sigma
    exact killed_row_noise_value P.npos S Good w g sigma i
  change historyExpectation (S.kernel P.npos) T (fun h => |pathSum
    (fun g sigma => ∑ j, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*w g j) h|) ≤ _
  rw [he]
  have hb : 0 ≤ (P.b/(P.a*eps))/n :=
    div_nonneg (div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le) (Nat.cast_nonneg n)
  exact killed_centered_path_abs_le (S.kernel P.npos) Good (fun g tau => w g (tau i))
    ((P.b/(P.a*eps))/n) hb
    (fun g tau => profileResponseWeight_bounds P eps heps T hdegree g.length i (tau i)) T

theorem profile_col_noise_abs_le {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (S : LatinRowPolicy n) (Good : LatinHistory n → Prop) (j : Fin n) :
    historyExpectation (S.kernel P.npos) T (fun h => |pathSum (fun g sigma =>
      ∑ i, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*
        profileResponseWeight P T g.length i j) h|) ≤
      Real.sqrt ((T : ℝ)*((P.b/(P.a*eps))/n)^2) := by
  let w : LatinHistory n → Fin n → ℝ := fun g i => profileResponseWeight P T g.length i j
  have he : (fun g sigma => ∑ i,
      killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*w g i) =
      killedCenteredValue (S.kernel P.npos) Good (fun g tau => w g (tau.symm j)) := by
    funext g sigma
    exact killed_col_noise_value P.npos S Good w g sigma j
  change historyExpectation (S.kernel P.npos) T (fun h => |pathSum
    (fun g sigma => ∑ i, killedRowNoise Good (fun g => permanentMarginal (S.matrix g)) g sigma i j*w g i) h|) ≤ _
  rw [he]
  have hb : 0 ≤ (P.b/(P.a*eps))/n :=
    div_nonneg (div_nonneg (P.a_pos.le.trans P.a_le_b) (mul_pos P.a_pos heps).le) (Nat.cast_nonneg n)
  exact killed_centered_path_abs_le (S.kernel P.npos) Good (fun g tau => w g (tau.symm j))
    ((P.b/(P.a*eps))/n) hb
    (fun g tau => profileResponseWeight_bounds P eps heps T hdegree g.length (tau.symm j) j) T

end LatinonEntropy

#print axioms LatinonEntropy.profile_row_noise_abs_le
#print axioms LatinonEntropy.profile_col_noise_abs_le
