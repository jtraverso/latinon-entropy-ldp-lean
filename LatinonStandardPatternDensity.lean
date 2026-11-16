module

public import LatinonC7Closure
public import Mathlib.Analysis.SpecialFunctions.Choose

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology Asymptotics
open scoped Classical

/-- The binomial normalization of Garbe et al., Definition 3.3. -/
def standardMatrixPatternDensity {n k l : ℕ} (L : LatinArray n)
    (P : LatinOrderPattern k l) : ℝ :=
  ((finiteMatrixPatternFamily L P).card : ℝ)/
    ((n.choose k : ℝ)*(n.choose l : ℝ))

def patternCoordinateFactor (n k l : ℕ) : ℝ :=
  ((n.descFactorial k : ℝ)/(n : ℝ)^k)*
    ((n.descFactorial l : ℝ)/(n : ℝ)^l)

theorem patternCoordinateFactor_tendsto_one (k l : ℕ) :
    Tendsto (fun n => patternCoordinateFactor n k l) atTop (𝓝 1) := by
  have h (j : ℕ) : Tendsto (fun n : ℕ => (n.descFactorial j : ℝ)/(n : ℝ)^j)
      atTop (𝓝 1) := by
    apply (isEquivalent_iff_tendsto_one ?_).mp (isEquivalent_descFactorial j)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  simpa only [patternCoordinateFactor,one_mul] using (h k).mul (h l)

theorem standardMatrixPatternDensity_eq_scaled {n k l : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (hl : l ≤ n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    standardMatrixPatternDensity L P=
      (patternCoordinateFactor n k l)⁻¹*finiteMatrixPatternDensity L P := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkR : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have hlR : (n.choose l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hl).ne'
  have hkF : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hlF : (l.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  unfold standardMatrixPatternDensity patternCoordinateFactor finiteMatrixPatternDensity
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [pow_add]
  field_simp

theorem finiteMatrixPatternDensity_mem_Icc {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finiteMatrixPatternDensity L P ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by unfold finiteMatrixPatternDensity; positivity,?_⟩
  have hmono := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (finitePatternSampleEvent_subset_pattern_ae hn L P))
  calc
    _ ≤ latinonPatternDensity (latinArrayToLatinonMeasure hn L) P := by
      rw [finiteMatrixPatternDensity_eq_sample_probability hn L P]
      exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
    _ ≤ 1 := (latinonPatternDensity_mem_Icc _ P).2

theorem standard_coordinate_pattern_error {n k l : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (hl : l ≤ n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    |standardMatrixPatternDensity L P-finiteMatrixPatternDensity L P| ≤
      |(patternCoordinateFactor n k l)⁻¹-1| := by
  obtain ⟨hzero,hone⟩ := finiteMatrixPatternDensity_mem_Icc hn L P
  rw [standardMatrixPatternDensity_eq_scaled hn hk hl L P]
  have heq : (patternCoordinateFactor n k l)⁻¹*finiteMatrixPatternDensity L P-
      finiteMatrixPatternDensity L P=
      ((patternCoordinateFactor n k l)⁻¹-1)*finiteMatrixPatternDensity L P := by ring
  rw [heq,abs_mul,abs_of_nonneg hzero]
  exact mul_le_of_le_one_right (abs_nonneg _) hone

theorem standard_pattern_normalization_error_tendsto_zero (k l : ℕ) :
    Tendsto (fun n => |(patternCoordinateFactor n k l)⁻¹-1|) atTop (𝓝 0) := by
  simpa using (((patternCoordinateFactor_tendsto_one k l).inv₀ (by norm_num)).sub_const 1).abs

def standardMatrixPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (L : LatinArray n) : J → ℝ :=
  fun j => standardMatrixPatternDensity L (P j)

theorem standard_pattern_profile_uniform_error {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n) (L : LatinArray n),
      dist (standardMatrixPatternProfile P L)
        (latinonPatternProfile P (latinArrayToLatinonMeasure (hN.trans_le hn) L)) < eps := by
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ j,
      |(patternCoordinateFactor n (k j) (l j))⁻¹-1| < eps/2 :=
    eventually_all.mpr (fun j => (standard_pattern_normalization_error_tendsto_zero (k j) (l j)).eventually
      (gt_mem_nhds (half_pos heps)))
  have hshape : ∀ᶠ n : ℕ in atTop, ∀ j, k j ≤ n ∧ l j ≤ n :=
    eventually_all.mpr (fun j => (eventually_ge_atTop (k j)).and (eventually_ge_atTop (l j)))
  obtain ⟨D,hD⟩ := eventually_atTop.mp (hsmall.and hshape)
  obtain ⟨E,hE,herror⟩ := finite_pattern_profile_uniform_error P (eps/2) (half_pos heps)
  let N := max E D
  have hN : 0 < N := hE.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn L
  have hnE : E ≤ n := (le_max_left _ _).trans hn
  have hnD : D ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := hN.trans_le hn
  have hc : dist (standardMatrixPatternProfile P L) (finiteMatrixPatternProfile P L) < eps/2 := by
    apply (dist_pi_lt_iff (half_pos heps)).mpr
    intro j
    change |standardMatrixPatternDensity L (P j)-finiteMatrixPatternDensity L (P j)| < eps/2
    exact (standard_coordinate_pattern_error hnp ((hD n hnD).2 j).1 ((hD n hnD).2 j).2 L (P j)).trans_lt
      ((hD n hnD).1 j)
  apply (dist_triangle _ (finiteMatrixPatternProfile P L) _).trans_lt
  linarith only [hc,herror n hnE L]

end LatinonEntropy

#print axioms LatinonEntropy.patternCoordinateFactor_tendsto_one
#print axioms LatinonEntropy.standardMatrixPatternDensity_eq_scaled
#print axioms LatinonEntropy.finiteMatrixPatternDensity_mem_Icc
#print axioms LatinonEntropy.standard_coordinate_pattern_error
#print axioms LatinonEntropy.standard_pattern_normalization_error_tendsto_zero
#print axioms LatinonEntropy.standard_pattern_profile_uniform_error
