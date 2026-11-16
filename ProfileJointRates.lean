module

public import ProfileFullCuts
public import UniformProfileSurvival
public import CutDensityBounds

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Filter Topology Finset
open scoped Classical

def profileClosenessRate (a b eps : ℝ) (m n : ℕ) : ℝ :=
  profileSurvivalRate a b eps m n+exponentialUnionRate 8 (eps^2/256) m n

theorem profile_full_bad_rate_bound {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (ha : P.a = a) (hb : P.b = b)
    (m : ℕ) (hm : Real.exp 2*fixedCorrectionUpper a b eps ≤ m)
    (hsize : permanentCapError m n ≤ (n : ℝ)/2) (T : ℕ) (hdegree : eps*n ≤ (n : ℝ)-T) :
    historyEventMass ((profileProcessPolicy P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4)).kernel P.npos) n
      (profileFullBad P eps heps (fixedCutDensity a b eps*(n : ℝ)^2/4) T (eps*(n : ℝ)^2/8)) ≤
      profileClosenessRate a b eps m n := by
  let delta := fixedCutDensity a b eps
  let v := delta*(n : ℝ)^2/4
  let u := eps*(n : ℝ)^2/8
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr P.npos)
  have hdelta : 0 < delta := fixedCutDensity_pos a b eps (ha ▸ P.a_pos) heps
  have hv : 0 < v := by dsimp [v]; positivity
  have hvsmall : v ≤ profileCutTolerance P eps heps/2 := by
    rw [profile_cut_tolerance_fixed P a b eps heps ha hb]
    dsimp [v,delta]
    have hpos := mul_pos hdelta (sq_pos_of_pos hn)
    dsimp [delta] at hpos
    linarith only [hpos]
  have hmP : Real.exp 2*(profileCorrectionParameters P eps heps).upper ≤ m := by
    rw [profile_upper_fixed P a b eps heps ha hb]; exact hm
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ (n : ℝ)*(2*(n : ℝ)) := by
    dsimp [u]
    nlinarith only [mul_le_mul_of_nonneg_right heps1 (sq_nonneg (n : ℝ)),sq_nonneg (n : ℝ)]
  have hmain := profile_principal_bad_mass_le P eps heps v hv T hdegree hvsmall m hmP hsize u hu0 hu
  have hcore := profile_finite_survival_error_le_rate P a b eps heps ha hb m T hdegree
  have hExp : (n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))) =
      2*(n : ℝ)*permanentCapError m n-(eps^2/256)*(n : ℝ)^2 := by
    dsimp [u]
    field_simp [hn.ne']
    ring
  have hpow : (8 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 8) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  have hmon : (8 : ℝ)^n*(2*Real.exp ((n : ℝ)*(2*permanentCapError m n)-u^2/(2*((n : ℝ)*(2*(n : ℝ)))))) ≤
      exponentialUnionRate 8 (eps^2/256) m n := by
    rw [hExp,hpow]
    calc
      _ = 2*Real.exp ((n : ℝ)*Real.log 8+(2*(n : ℝ)*permanentCapError m n-(eps^2/256)*(n : ℝ)^2)) := by
        rw [Real.exp_add]; ring
      _ ≤ 2*(n : ℝ)*Real.exp ((n : ℝ)*Real.log 8+(2*(n : ℝ)*permanentCapError m n-(eps^2/256)*(n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hn1]) (Real.exp_pos _).le
      _ = _ := by unfold exponentialUnionRate; congr 2; ring
  have hfull := profile_full_bad_mass_le_principal P eps heps v T (P.main_index eps heps T hdegree).le u
    ((profileProcessPolicy P eps heps v).kernel P.npos)
  exact hfull.trans (hmain.trans (add_le_add hcore hmon))

theorem profile_closeness_rate_log_sq_tendsto_zero (a b eps : ℝ) (ha : 0 < a) (heps : 0 < eps) (m : ℕ) :
    Tendsto (fun n : ℕ => profileClosenessRate a b eps m n*Real.log (n : ℝ)^2) atTop (𝓝 0) := by
  have h1 := profile_survival_rate_log_sq_tendsto_zero a b eps ha heps m
  have h2 := exponential_union_rate_log_sq_tendsto_zero 8 (eps^2/256)
    (div_pos (sq_pos_of_pos heps) (by norm_num)) m
  have he : (fun n : ℕ => profileClosenessRate a b eps m n*Real.log (n : ℝ)^2) =
      (fun n : ℕ => profileSurvivalRate a b eps m n*Real.log (n : ℝ)^2+
        exponentialUnionRate 8 (eps^2/256) m n*Real.log (n : ℝ)^2) := by
    funext n; unfold profileClosenessRate; ring
  rw [he]
  simpa using h1.add h2

end LatinonEntropy

#print axioms LatinonEntropy.profile_full_bad_rate_bound
#print axioms LatinonEntropy.profile_closeness_rate_log_sq_tendsto_zero
