module

public import ProfileEntropyError
public import EntropyRateAsymptotics

@[expose] public section

noncomputable section

namespace LatinonEntropy

/-- The finite process entropy loss is bounded by a scalar rate depending
only on the fixed entry bounds, the truncation, and the permanent index. -/
theorem profile_entropy_error_le_rate {n : ℕ} (P : PositiveLatinProfile n)
    (a b eps : ℝ) (heps : 0 < eps) (ha : P.a = a) (hb : P.b = b) (m : ℕ) :
    (n : ℝ)*profileRowEntropyError P a b eps heps m+(n : ℝ)*Real.log (n : ℝ) ≤
      (n : ℝ)^2*profileEntropyRate a b eps m n := by
  let c := b/(a*eps)
  let G := fixedEntropyLogConstant a b eps
  let J := Real.log (n : ℝ)+|Real.log a|
  let L := Real.log (n : ℝ)+G+1
  let B := Real.sqrt (2*(n : ℝ)*permanentCapError m n)
  let D := profileStabilityBound P eps m
  let R := profileSurvivalRate a b eps m n
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.npos
  have hG : 0 ≤ G := by unfold G fixedEntropyLogConstant; positivity
  have hL : 0 ≤ L := add_nonneg (add_nonneg (Real.log_natCast_nonneg n) hG) (by norm_num)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hD : 0 ≤ D := profileStabilityBound_nonneg P eps heps m
  have hW : profileEntropyWeightCap P eps = c/n*J := by
    simp only [profileEntropyWeightCap,ha,hb,c,J]
  have he : profileRowEntropyError P a b eps heps m =
      G*B+3*L*D+c*J*(B+3*D)+(n : ℝ)*c*J*R := by
    unfold profileRowEntropyError
    rw [profile_entropy_log_constant_fixed P a b eps heps ha hb,hW]
    dsimp only [G,L,B,D,R]
    field_simp [hn.ne']
  have hsum : profileRowEntropyError P a b eps heps m ≤
      (G+L+c*J)*(B+3*D)+(n : ℝ)*c*J*R := by
    rw [he]
    nlinarith only [mul_nonneg hG hD,mul_nonneg hL hB]
  have hd := profile_normalized_drift_bound_identity P eps m
  rw [ha,hb] at hd
  have hdn : B+3*D = profileDriftRate c m n*(n : ℝ) :=
    (div_eq_iff hn.ne').mp hd
  calc
    _ ≤ (n : ℝ)*((G+L+c*J)*(B+3*D)+(n : ℝ)*c*J*R)+(n : ℝ)*Real.log (n : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum hn.le) le_rfl
    _ = _ := by
      rw [hdn]
      unfold profileEntropyRate
      dsimp only [c,G,J,L,R]
      field_simp [hn.ne']
      ring

end LatinonEntropy

#print axioms LatinonEntropy.profile_entropy_error_le_rate
