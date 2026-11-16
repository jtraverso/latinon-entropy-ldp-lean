module

public import ProfileRowGuard
public import HistoryPropagation

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset

def profileCellDefect {n : ℕ} (P : PositiveLatinProfile n) (Good : LatinHistory n → Prop)
    (h : LatinHistory n) (i j : Fin n) : ℝ :=
  stoppedAvailability Good (profileHazard P) h i j-profileRemaining P h.length i j

def profileCellError {n : ℕ} (P : PositiveLatinProfile n) (Good : LatinHistory n → Prop)
    (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ) (h : LatinHistory n)
    (sigma : Equiv.Perm (Fin n)) (i j : Fin n) : ℝ :=
  killedRowNoise Good m h sigma i j+killedRowDrift Good (profileHazard P) m h i j

def profileResponseWeight {n : ℕ} (P : PositiveLatinProfile n) (T t : ℕ) (i j : Fin n) : ℝ :=
  propagationKernel (fun s => profileHazard P s i j) t T*profileHazard P T i j

theorem profileResponseWeight_bounds {n : ℕ} (P : PositiveLatinProfile n)
    (eps : ℝ) (heps : 0 < eps) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T)
    (t : ℕ) (i j : Fin n) :
    0 ≤ profileResponseWeight P T t i j ∧ profileResponseWeight P T t i j ≤ (P.b/(P.a*eps))/n := by
  have hk := propagationKernel_bounds (fun s => profileHazard P s i j)
    (fun s => P.hazard_mem_unit s i j) t T
  have hh := P.hazard_mem_unit T i j
  refine ⟨mul_nonneg hk.1 hh.1,?_⟩
  exact (mul_le_mul_of_nonneg_right hk.2 hh.1).trans
    (by simpa only [one_mul] using (P.hazard_main_bounds eps heps T hdegree i j).2)

theorem profile_cell_propagation {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (i j : Fin n) :
    profileCellDefect P Good h i j = -pathSum (fun g sigma =>
      propagationKernel (fun s => profileHazard P s i j) g.length h.length*
        profileCellError P Good m g sigma i j) h := by
  apply history_defect_at_horizon LatinHistoryValid (fun _ _ hh => hh.1)
    (fun h => profileCellDefect P Good h i j) (fun t => profileHazard P t i j)
    (fun g sigma => profileCellError P Good m g sigma i j) ?_ ?_ h hv
  · exact profile_fluid_defect_initial P Good i j
  · intro sigma g hg
    simpa only [profileCellDefect,profileCellError,List.length_cons,sub_add_eq_sub_sub]
      using actual_profile_fluid_defect_step P Good m g sigma hg i j

theorem profile_row_propagation {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (ht : h.length < n) (i : Fin n) :
    (∑ j, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1 =
      -pathSum (fun g sigma => ∑ j, profileResponseWeight P h.length g.length i j*
        profileCellError P Good m g sigma i j) h := by
  have hs : pathSum (fun g sigma => ∑ j, profileResponseWeight P h.length g.length i j*
      profileCellError P Good m g sigma i j) h =
      ∑ j, profileHazard P h.length i j*pathSum (fun g sigma =>
        propagationKernel (fun s => profileHazard P s i j) g.length h.length*
          profileCellError P Good m g sigma i j) h := by
    rw [pathSum_sum]
    apply sum_congr rfl
    intro j _
    have he : (fun g sigma => profileResponseWeight P h.length g.length i j*
        profileCellError P Good m g sigma i j) =
        (fun g sigma => profileHazard P h.length i j*
          (propagationKernel (fun s => profileHazard P s i j) g.length h.length*
            profileCellError P Good m g sigma i j)) := by
      funext g sigma
      unfold profileResponseWeight
      ring
    rw [he,pathSum_mul]
  rw [hs]
  calc
    _ = ∑ j, profileCellDefect P Good h i j*profileHazard P h.length i j :=
      profile_auxiliary_row_defect P Good h ht i
    _ = _ := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro j _
      rw [profile_cell_propagation P Good m h hv i j]
      ring

theorem profile_col_propagation {n : ℕ} (P : PositiveLatinProfile n)
    (Good : LatinHistory n → Prop) (m : LatinHistory n → Matrix (Fin n) (Fin n) ℝ)
    (h : LatinHistory n) (hv : LatinHistoryValid h) (ht : h.length < n) (j : Fin n) :
    (∑ i, stoppedAvailability Good (profileHazard P) h i j*profileHazard P h.length i j)-1 =
      -pathSum (fun g sigma => ∑ i, profileResponseWeight P h.length g.length i j*
        profileCellError P Good m g sigma i j) h := by
  have hs : pathSum (fun g sigma => ∑ i, profileResponseWeight P h.length g.length i j*
      profileCellError P Good m g sigma i j) h =
      ∑ i, profileHazard P h.length i j*pathSum (fun g sigma =>
        propagationKernel (fun s => profileHazard P s i j) g.length h.length*
          profileCellError P Good m g sigma i j) h := by
    rw [pathSum_sum]
    apply sum_congr rfl
    intro i _
    have he : (fun g sigma => profileResponseWeight P h.length g.length i j*
        profileCellError P Good m g sigma i j) =
        (fun g sigma => profileHazard P h.length i j*
          (propagationKernel (fun s => profileHazard P s i j) g.length h.length*
            profileCellError P Good m g sigma i j)) := by
      funext g sigma
      unfold profileResponseWeight
      ring
    rw [he,pathSum_mul]
  rw [hs]
  calc
    _ = ∑ i, profileCellDefect P Good h i j*profileHazard P h.length i j :=
      profile_auxiliary_col_defect P Good h ht j
    _ = _ := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      rw [profile_cell_propagation P Good m h hv i j]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.profile_cell_propagation
#print axioms LatinonEntropy.profile_row_propagation
#print axioms LatinonEntropy.profile_col_propagation
