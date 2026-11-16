module

public import LatinonFinitePatternBridge
public import LatinonBridge.LocalObservableEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

def finiteMatrixPatternProfile {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (L : LatinArray n) : J → ℝ :=
  fun j => finiteMatrixPatternDensity L (P j)

def finiteMatrixPatternBallFamily {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ) (rho : ℝ) (n : ℕ)
    [Fintype J] : Finset (LatinArray n) :=
  (allLatinSquares n).filter (fun L => finiteMatrixPatternProfile P L ∈ Metric.ball z rho)

theorem patternBridgeConstant_nonneg (k l : ℕ) : 0 ≤ patternBridgeConstant k l := by
  unfold patternBridgeConstant
  positivity

theorem finite_matrix_pattern_profile_error {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) {n : ℕ} (hn : 0 < n) (L : LatinArray n) :
    dist (finiteMatrixPatternProfile P L) (latinonPatternProfile P (latinArrayToLatinonMeasure hn L)) ≤
      (∑ j, patternBridgeConstant (k j) (l j))/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : 0 ≤ ∑ j, patternBridgeConstant (k j) (l j) :=
    Finset.sum_nonneg (fun j _ => patternBridgeConstant_nonneg _ _)
  apply (dist_pi_le_iff (div_nonneg hsum hnR.le)).mpr
  intro j
  change |finiteMatrixPatternDensity L (P j)-latinonPatternDensity (latinArrayToLatinonMeasure hn L) (P j)| ≤ _
  rw [abs_sub_comm]
  exact (finite_matrix_pattern_embedding_error hn L (P j)).trans
    ((div_le_div_iff_of_pos_right hnR).mpr
      (Finset.single_le_sum (fun i _ => patternBridgeConstant_nonneg (k i) (l i)) (Finset.mem_univ j)))

theorem finite_pattern_profile_uniform_error {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n) (L : LatinArray n),
      dist (finiteMatrixPatternProfile P L)
        (latinonPatternProfile P (latinArrayToLatinonMeasure (hN.trans_le hn) L)) < eps := by
  let B := ∑ j, patternBridgeConstant (k j) (l j)
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1 : ℝ) (B/eps))
  have hNpos : 0 < N := Nat.cast_pos.mp (lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN))
  refine ⟨N,hNpos,?_⟩
  intro n hn L
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hNpos.trans_le hn)
  have hlarge : B/eps < (n : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le (Nat.cast_le.mpr hn)
  have hfrac : B/(n : ℝ) < eps :=
    (div_lt_iff₀ hnR).mpr (by simpa only [mul_comm] using (div_lt_iff₀ heps).mp hlarge)
  exact (finite_matrix_pattern_profile_error P _ L).trans_lt hfrac

/-- Microcanonical counts for explicit finite MATRIX statistics, with
the contracted cost of actual Latinon pattern densities. -/
theorem finite_rate_finite_pattern_entropy_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonPatternProfile P) z).toReal-eta)) ≤
          ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ∧
      ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
          (latinonContractedRate (latinonPatternProfile P) z).toReal+eta)) := by
  let T := latinonPatternProfile P
  have hT : Continuous T := continuous_latinonPatternProfile P
  obtain ⟨rho,hrho,hrhor,U,hU,hupper⟩ := finite_rate_observable_entropy_count T hT z hfinite r eta hr heta
  obtain ⟨sigma,hsigma,hsigmar,V,hV,hlower⟩ :=
    finite_rate_observable_entropy_count T hT z hfinite (rho/4) eta (by positivity) heta
  obtain ⟨E,hE,herror⟩ := finite_pattern_profile_uniform_error P (rho/4) (by positivity)
  let N := max U (max V E)
  have hN : 0 < N := hU.trans_le (le_max_left _ _)
  refine ⟨rho/2,half_pos hrho,by linarith,N,hN,?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnV : V ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnE : E ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnp : 0 < n := hN.trans_le hn
  have herr (L : LatinArray n) :
      dist (finiteMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) < rho/4 := herror n hnE L
  have hsubL : latinonEventLatinFamily (hV.trans_le hnV) (T ⁻¹' Metric.ball z sigma) ⊆
      finiteMatrixPatternBallFamily P z (rho/2) n := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (finiteMatrixPatternProfile P L) z < rho/2
    have hb : dist (T (latinArrayToLatinonMeasure hnp L)) z < sigma := hball
    have ht := dist_triangle (finiteMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) z
    have he := herr L
    linarith
  have hsubU : finiteMatrixPatternBallFamily P z (rho/2) n ⊆
      latinonEventLatinFamily (hU.trans_le hnU) (T ⁻¹' Metric.ball z rho) := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z < rho
    have hb : dist (finiteMatrixPatternProfile P L) z < rho/2 := hball
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) < rho/4 := by
      rw [dist_comm]
      exact herr L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) z
    linarith
  exact ⟨((hlower n hnV).1).trans (Nat.cast_le.mpr (Finset.card_le_card hsubL)),
    (Nat.cast_le.mpr (Finset.card_le_card hsubU)).trans ((hupper n hnU).2)⟩

theorem empty_pattern_profile_fiber_rate_top {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (h : ¬∃ W : LatinonMeasure, latinonPatternProfile P W=z) :
    latinonContractedRate (latinonPatternProfile P) z=⊤ :=
  latinonContractedRate_outside_image _ _ h

/-- Infinite contracted cost gives arbitrary finite exponential upper
penalties.Never interprets the real value of infinity. -/
theorem infinite_rate_finite_pattern_count_upper {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hinfinite : latinonContractedRate (latinonPatternProfile P) z=⊤)
    (r t eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      ((finiteMatrixPatternBallFamily P z rho n).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eta)) := by
  let T := latinonPatternProfile P
  have hT : Continuous T := continuous_latinonPatternProfile P
  have hstrict : ENNReal.ofReal t < latinonContractedRate T z := by
    rw [hinfinite]
    exact ENNReal.ofReal_lt_top
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp
    (latinonContractedRate_lowerSemicontinuous T hT z (ENNReal.ofReal t) hstrict)
  let rho := min r (delta/4)
  have hrho : 0 < rho := lt_min hr (by positivity)
  have hfloor : ∀ z' ∈ Metric.closedBall z (delta/2), ENNReal.ofReal t ≤ latinonContractedRate T z' := by
    intro z' hz'
    have hzdist : dist z' z ≤ delta/2 := hz'
    have hzin : z' ∈ Metric.ball z delta := hzdist.trans_lt (by linarith)
    exact le_of_lt (hball hzin)
  obtain ⟨U,hU,hupper⟩ := closed_observable_latin_count_upper T hT (Metric.closedBall z (delta/2))
    Metric.isClosed_closedBall t hfloor eta heta
  obtain ⟨E,hE,herror⟩ := finite_pattern_profile_uniform_error P rho hrho
  let N := max U E
  refine ⟨rho,hrho,min_le_left _ _,N,hU.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnE : E ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := hU.trans_le hnU
  have hsub : finiteMatrixPatternBallFamily P z rho n ⊆
      latinonEventLatinFamily hnp (T ⁻¹' Metric.closedBall z (delta/2)) := by
    intro L hL
    obtain ⟨hAll,hb⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z ≤ delta/2
    have hdist : dist (finiteMatrixPatternProfile P L) z < rho := hb
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) < rho := by
      rw [dist_comm]
      exact herror n hnE L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (finiteMatrixPatternProfile P L) z
    have hrhod : rho ≤ delta/4 := min_le_right _ _
    linarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hupper n hnU)

end LatinonEntropy

#print axioms LatinonEntropy.patternBridgeConstant_nonneg
#print axioms LatinonEntropy.finite_matrix_pattern_profile_error
#print axioms LatinonEntropy.finite_pattern_profile_uniform_error
#print axioms LatinonEntropy.finite_rate_finite_pattern_entropy_count
#print axioms LatinonEntropy.empty_pattern_profile_fiber_rate_top
#print axioms LatinonEntropy.infinite_rate_finite_pattern_count_upper
