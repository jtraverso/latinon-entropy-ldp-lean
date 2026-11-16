module

public import LatinonCoarseApproximation
public import LatinonPatternAlignment

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonPatternDensity_alignment_bound {k l q : ℕ} (W V : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) (e f : LatinonRelabel) :
    |latinonPatternDensity W P-latinonPatternDensity V P| ≤
      2*(((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ))+
        (patternPolynomialConstant P q : ℝ)*latinonAlignmentCost W V e f := by
  have hW := latinonPatternDensity_polynomial_error W P hq
  have hV := latinonPatternDensity_polynomial_error V P hq
  have hpoly := compressionPatternPolynomial_alignment W V P q e f
  have h1 := abs_sub_le (latinonPatternDensity W P) (compressionPatternPolynomial W P q)
    (latinonPatternDensity V P)
  have h2 := abs_sub_le (compressionPatternPolynomial W P q) (compressionPatternPolynomial V P q)
    (latinonPatternDensity V P)
  rw [abs_sub_comm (compressionPatternPolynomial V P q)] at h2
  linarith

/-- Actual pattern densities are uniformly continuous for the full
original cut pseudometric, with both order terms and no rate hypothesis. -/
theorem uniformContinuous_latinonPatternDensity {k l : ℕ} (P : LatinOrderPattern k l) :
    UniformContinuous (fun W : LatinonMeasure => latinonPatternDensity W P) := by
  apply Metric.uniformContinuous_iff.mpr
  intro eta heta
  let B : ℝ := ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2
  obtain ⟨q,hqR⟩ := exists_nat_gt (max (1 : ℝ) (4*B/eta))
  have hqposR : (0 : ℝ) < q := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hqR)
  have hq : 0 < q := Nat.cast_pos.mp hqposR
  have hB : 2*B/(q : ℝ) < eta/2 := by
    apply (div_lt_iff₀ hqposR).mpr
    have h := (div_lt_iff₀ heta).mp ((le_max_right _ _).trans_lt hqR)
    nlinarith
  rw [mul_div_assoc] at hB
  let C : ℝ := (patternPolynomialConstant P q : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let delta := eta/(2*(C+1))
  have hden : 0 < 2*(C+1) := by positivity
  have hdelta : 0 < delta := div_pos heta hden
  refine ⟨delta,hdelta,?_⟩
  intro W V hdist
  obtain ⟨e,f,hef⟩ := exists_alignmentCost_lt W V delta hdist
  have hb := latinonPatternDensity_alignment_bound W V P hq e f
  have hc : C*latinonAlignmentCost W V e f ≤ eta/2 := by
    calc
      _ ≤ C*delta := mul_le_mul_of_nonneg_left hef.le hC
      _ ≤ (C+1)*delta := mul_le_mul_of_nonneg_right (by linarith) hdelta.le
      _ = eta/2 := by
        dsimp [delta]
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < C+1)]
  rw [Real.dist_eq]
  change |latinonPatternDensity W P-latinonPatternDensity V P| < eta
  change |latinonPatternDensity W P-latinonPatternDensity V P| ≤ 2*(B/(q : ℝ))+
    C*latinonAlignmentCost W V e f at hb
  linarith

theorem continuous_latinonPatternDensity {k l : ℕ} (P : LatinOrderPattern k l) :
    Continuous (fun W : LatinonMeasure => latinonPatternDensity W P) :=
  (uniformContinuous_latinonPatternDensity P).continuous

def latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (W : LatinonMeasure) : J → ℝ :=
  fun j => latinonPatternDensity W (P j)

theorem continuous_latinonPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) : Continuous (latinonPatternProfile P) :=
  continuous_pi (fun j => continuous_latinonPatternDensity (P j))

end LatinonEntropy

#print axioms LatinonEntropy.latinonPatternDensity_alignment_bound
#print axioms LatinonEntropy.uniformContinuous_latinonPatternDensity
#print axioms LatinonEntropy.continuous_latinonPatternDensity
#print axioms LatinonEntropy.continuous_latinonPatternProfile
