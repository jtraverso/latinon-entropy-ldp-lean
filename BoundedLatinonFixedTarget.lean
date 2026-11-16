module

public import GridDistributionApproximation
public import GridProfilePermutation
public import BoundedLatinonRate
public import UniformLatinonGridLower

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem finite_rate_grid_density_entropy_lower (W : LatinonMeasure) (hfinite : latinonRate W ≠ ⊤)
    {n : ℕ} (hn : 0 < n) :
    -(latinonRate W).toReal ≤ latinGridDensityEntropy
      (fun (x y z : Fin n) => (n : ℝ)*latinonGridTensor W x y z) := by
  have he := latinon_grid_density_divergence_le W hn
  rw [← ENNReal.ofReal_toReal hfinite] at he
  have hr := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp he
  linarith only [hr]

/-- Actual fixed-target approximation in the FULL Latinon metric,
with uniform positive profile bounds and the required entropy direction.
Every large n is covered; no approximation or alignment is assumed. -/
theorem exists_bounded_latinon_profile_approximation (W : LatinonMeasure) (a b : ℝ)
    (ha : 0 < a) (h : HasLatinonDensityBounds W a b) (rho : ℝ) (hrho : 0 < rho) :
    ∃ (N : ℕ) (_hN : 0 < N), ∀ (n : ℕ) (_hn : N ≤ n), ∃ P : PositiveLatinProfile n,
      P.a = a ∧ P.b = b ∧ dist W (profileToLatinonMeasure P) < rho ∧
        -(latinonRate W).toReal ≤ latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z) := by
  have hac : W.measure ≪ unitCubeVolume := bounded_latinon_absolutelyContinuous W a b h
  have hfinite := bounded_latinon_rate_ne_top W a b ha h
  obtain ⟨ND,hND,hD⟩ := exists_all_sizes_grid_distribution_cut W hac (rho/4) (by positivity)
  obtain ⟨NO,hNO,hO⟩ := exists_all_sizes_orderCut_permutation W.order W.order_preserving (rho/8) (by positivity)
  let N := max ND NO
  have hN : 0 < N := hND.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnD : ND ≤ n := (le_max_left _ _).trans hn
  have hnO : NO ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := hN.trans_le hn
  let P := boundedLatinonGridProfile W a b ha h n hnpos
  obtain ⟨sigma,horder⟩ := hO n hnO
  let Q := permutePositiveLatinProfile P sigma
  let e := gridIntervalRelabel hnpos sigma
  let V := profileToLatinonMeasure Q
  refine ⟨Q,rfl,rfl,?_,?_⟩
  · have hd := hD n hnD
    change measureCut W.measure (profileToLatinonMeasure P).measure ≤ rho/4 at hd
    change orderCut W.order e < rho/8 at horder
    have hmeasure : relabelLatinonMeasure V.measure e e = (profileToLatinonMeasure P).measure :=
      permuted_profile_relabel_measure P sigma
    have hcost : latinonAlignmentCost W V e e < rho := by
      change orderCut W.order e+orderCut W.order e+
        measureCut W.measure (relabelLatinonMeasure V.measure e e) < rho
      rw [hmeasure]
      linarith only [horder,hd,hrho]
    change latinonCutDistance W V < rho
    exact (latinonCutDistance_le_cost W V e e).trans_lt hcost
  · rw [permute_profile_density_entropy P sigma]
    exact finite_rate_grid_density_entropy_lower W hfinite hnpos

/-- Lower large-deviation bound at the ACTUAL fixed continuous centre W,
for bounded positive densities,with its actual continuum KL rate. -/
theorem bounded_uniform_latinon_local_lower (W : LatinonMeasure) (a b : ℝ)
    (ha : 0 < a) (h : HasLatinonDensityBounds W a b) (rho eta : ℝ)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) ≤
        (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W rho) := by
  obtain ⟨NA,hNA,happrox⟩ := exists_bounded_latinon_profile_approximation W a b ha h (rho/2) (half_pos hrho)
  obtain ⟨NC,hNC,hcount⟩ := uniform_latinon_grid_ball_lower a b (rho/2) eta ha (half_pos hrho) heta
  let N := max NA NC
  have hN : 0 < N := hNA.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnA : NA ≤ n := (le_max_left _ _).trans hn
  have hnC : NC ≤ n := (le_max_right _ _).trans hn
  obtain ⟨P,hPa,hPb,hd,hE⟩ := happrox n hnA
  have hprob := hcount n hnC P hPa hPb
  have hsubset : Metric.ball (profileToLatinonMeasure P) (rho/2) ⊆ Metric.ball W rho := by
    intro V hV
    change dist V (profileToLatinonMeasure P) < rho/2 at hV
    change dist V W < rho
    have hsym : dist (profileToLatinonMeasure P) W < rho/2 := by simpa only [dist_comm] using hd
    exact (dist_triangle V (profileToLatinonMeasure P) W).trans_lt (by linarith only [hV,hsym])
  calc
    Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta)) ≤
        Real.exp ((n : ℝ)^2*(latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z)-eta)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith only [hE]) (sq_nonneg (n : ℝ))
    _ ≤ (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball (profileToLatinonMeasure P) (rho/2)) := hprob
    _ ≤ (uniformLatinonLaw (hN.trans_le hn)).real (Metric.ball W rho) :=
      measureReal_mono hsubset (measure_ne_top (uniformLatinonLaw (hN.trans_le hn)) _)

/-- Continuum entropy lower count at the fixed bounded positive Latinon,
in the actual full metric and with the exact second-order constant -2. -/
theorem bounded_latinon_fixed_target_count_lower (W : LatinonMeasure) (a b : ℝ)
    (ha : 0 < a) (h : HasLatinonDensityBounds W a b) (rho eta : ℝ)
    (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) := by
  obtain ⟨NP,hNP,hprob⟩ := bounded_uniform_latinon_local_lower W a b ha h rho (eta/2) hrho (half_pos heta)
  obtain ⟨NT,hNT,htotal⟩ := total_latin_square_count_normalization (eta/2) (half_pos heta)
  let N := max NP NT
  have hN : 0 < N := hNP.trans_le (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnP : NP ≤ n := (le_max_left _ _).trans hn
  have hnT : NT ≤ n := (le_max_right _ _).trans hn
  have hp := hprob n hnP
  rw [uniformLatinonLaw_real_ball] at hp
  have hcardpos : (0 : ℝ) < (allLatinSquares n).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (allLatinSquares_nonempty n (hN.trans_le hn)))
  have hmul := (le_div_iff₀ hcardpos).mp hp
  calc
    Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) =
      Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta/2))*
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-eta/2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp ((n : ℝ)^2*(-(latinonRate W).toReal-eta/2))*(allLatinSquares n).card :=
      mul_le_mul_of_nonneg_left (htotal n hnT).1 (Real.exp_pos _).le
    _ ≤ ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) := hmul

/-- The entropy counting formula at every bounded positive Latinon,with
an arbitrarily small full-metric ball and both exponential inequalities. -/
theorem bounded_latinon_entropy_count (W : LatinonMeasure) (a b : ℝ)
    (ha : 0 < a) (h : HasLatinonDensityBounds W a b) (r eta : ℝ)
    (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal-eta)) ≤
        ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) ∧
      ((latinonBallLatinFamily (hN.trans_le hn) W rho).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonRate W).toReal+eta)) := by
  have hfinite := bounded_latinon_rate_ne_top W a b ha h
  obtain ⟨delta,hd,NU,hNU,hupper⟩ := exists_finite_rate_latinon_local_upper W hfinite eta heta
  let rho := min delta r
  have hrho : 0 < rho := lt_min hd hr
  obtain ⟨NL,hNL,hlower⟩ := bounded_latinon_fixed_target_count_lower W a b ha h rho eta hrho heta
  let N := max NL NU
  have hN : 0 < N := hNL.trans_le (le_max_left _ _)
  refine ⟨rho,hrho,min_le_right _ _,N,hN,?_⟩
  intro n hn
  have hnL : NL ≤ n := (le_max_left _ _).trans hn
  have hnU : NU ≤ n := (le_max_right _ _).trans hn
  refine ⟨hlower n hnL,?_⟩
  apply hupper n hnU (latinonBallLatinFamily (hN.trans_le hn) W rho)
  intro L hL
  have hm := (Finset.mem_filter.mp hL).2
  change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) W < rho at hm
  change dist (latinArrayToLatinonMeasure (hN.trans_le hn) L) W < delta
  exact hm.trans_le (min_le_left _ _)

end LatinonEntropy

#print axioms LatinonEntropy.finite_rate_grid_density_entropy_lower
#print axioms LatinonEntropy.exists_bounded_latinon_profile_approximation
#print axioms LatinonEntropy.bounded_uniform_latinon_local_lower
#print axioms LatinonEntropy.bounded_latinon_fixed_target_count_lower
#print axioms LatinonEntropy.bounded_latinon_entropy_count
