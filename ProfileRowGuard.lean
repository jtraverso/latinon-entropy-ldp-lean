module

public import ProfileFluid
public import CorrectedRowPolicy
public import StoppedAvailability

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileCorrectionParameters {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) : RowCorrectionParameters where
  eps := eps
  rho := min 1 (P.a*eps/2)
  a := P.a
  c := max P.a (P.b/(P.a*eps))
  eps_pos := heps
  rho_pos := lt_min (by norm_num) (half_pos (mul_pos P.a_pos heps))
  rho_le := min_le_left _ _
  a_pos := P.a_pos
  a_le_c := le_max_left _ _

def profileCandidate {n : ℕ} (P : PositiveLatinProfile n) (h : LatinHistory n) (i j : Fin n) : ℝ :=
  availability h i j*profileHazard P h.length i j

/-- With the actual p/R hazard, the only extra guard input in the main
range is the cut condition. Entry and support hypotheses are derived. -/
theorem correctable_profile_history {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (h : LatinHistory n) (hv : LatinHistoryValid h)
    (hdegree : eps*n ≤ (n : ℝ)-h.length)
    (hcut : ∀ S T : Finset (Fin n),
      (profileCorrectionParameters P eps heps).rho*S.card*T.card-
        (profileCorrectionParameters P eps heps).rho*eps*(n : ℝ)^2/
          (64*(profileCorrectionParameters P eps heps).upper) ≤ rectMass (availability h) S T) :
    CorrectableHistory (profileCorrectionParameters P eps heps) (profileCandidate P) h := by
  refine { valid := hv, degree := hdegree, cut := hcut, zero := ?_, entries := ?_ }
  · intro i j hz
    simp only [profileCandidate,hz,zero_mul]
  · intro i j ho
    have hb := P.hazard_main_bounds eps heps h.length hdegree i j
    have hu : profileHazard P h.length i j ≤ max P.a (P.b/(P.a*eps))/n :=
      hb.2.trans (div_le_div_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg n))
    simpa only [profileCandidate,ho,one_mul,profileCorrectionParameters] using And.intro hb.1 hu

theorem actual_profile_fluid_defect_step {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (sigma : Equiv.Perm (Fin n)) (hv : LatinHistoryValid (sigma::h)) (i j : Fin n) :
    stoppedAvailability Good (profileHazard P) (sigma::h) i j-profileRemaining P (h.length+1) i j =
      (stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j)*
        (1-profileHazard P h.length i j)-killedRowNoise Good m h sigma i j-
        killedRowDrift Good (profileHazard P) m h i j :=
  stopped_fluid_defect_step Good (profileHazard P) (profileRemaining P) m P.fluid_step h sigma hv i j

theorem profile_fluid_defect_initial {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (i j : Fin n) :
    stoppedAvailability Good (profileHazard P) [] i j-profileRemaining P 0 i j = 0 := by
  simp [stoppedAvailability,availability,usedSymbols,P.remaining_initial]

theorem profile_auxiliary_row_defect {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (ht : h.length < n) (i : Fin n) :
    (∑ j, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1 =
      ∑ j, (stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j)*
        profileHazard P h.length i j := by
  have hr : (∑ j, profileRemaining P h.length i j*profileHazard P h.length i j) = 1 := by
    simp_rw [P.remaining_hazard h.length ht]
    exact P.row_mass ⟨h.length,ht⟩ i
  simp only [sub_mul,sum_sub_distrib]
  rw [hr]

theorem profile_auxiliary_col_defect {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (h : LatinHistory n) (ht : h.length < n) (j : Fin n) :
    (∑ i, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1 =
      ∑ i, (stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j)*
        profileHazard P h.length i j := by
  have hr : (∑ i, profileRemaining P h.length i j*profileHazard P h.length i j) = 1 := by
    simp_rw [P.remaining_hazard h.length ht]
    exact P.col_mass ⟨h.length,ht⟩ j
  simp only [sub_mul,sum_sub_distrib]
  rw [hr]

end LatinonEntropy

#print axioms LatinonEntropy.correctable_profile_history
#print axioms LatinonEntropy.actual_profile_fluid_defect_step
#print axioms LatinonEntropy.profile_auxiliary_row_defect
