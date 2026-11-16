module

public import LatinonStandardPatternDensity

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

/-- Closed pattern boxes with the binomial normalization of Definition 3.3. -/
def standardMatrixPatternBoxFamily {J : Type*} {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ) (rho : ℝ) (n : ℕ)
    [Fintype J] : Finset (LatinArray n) :=
  (allLatinSquares n).filter (fun L => standardMatrixPatternProfile P L ∈ Metric.closedBall z rho)

theorem mem_standardMatrixPatternBoxFamily_iff {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    {n : ℕ} (L : LatinArray n) :
    L ∈ standardMatrixPatternBoxFamily P z rho n ↔
      ∀ j, |standardMatrixPatternDensity L (P j)-z j| ≤ rho := by
  simp only [standardMatrixPatternBoxFamily,Finset.mem_filter,allLatinSquares,Finset.mem_univ,true_and,
    Metric.mem_closedBall,dist_pi_le_iff hrho,Real.dist_eq,standardMatrixPatternProfile]

/-- The finite-cost entropy count for the published finite-pattern convention. -/
theorem finite_rate_standard_pattern_entropy_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonPatternProfile P) z).toReal-eta)) ≤
          ((standardMatrixPatternBoxFamily P z rho n).card : ℝ) ∧
      ((standardMatrixPatternBoxFamily P z rho n).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
          (latinonContractedRate (latinonPatternProfile P) z).toReal+eta)) := by
  let T := latinonPatternProfile P
  have hT : Continuous T := continuous_latinonPatternProfile P
  obtain ⟨rho,hrho,hrhor,U,hU,hupper⟩ := finite_rate_observable_entropy_count T hT z hfinite r eta hr heta
  obtain ⟨sigma,hsigma,hsigmar,V,hV,hlower⟩ :=
    finite_rate_observable_entropy_count T hT z hfinite (rho/4) eta (by positivity) heta
  obtain ⟨E,hE,herror⟩ := standard_pattern_profile_uniform_error P (rho/4) (by positivity)
  let N := max U (max V E)
  have hN : 0 < N := hU.trans_le (le_max_left _ _)
  refine ⟨rho/2,half_pos hrho,by linarith,N,hN,?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnV : V ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnE : E ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnp : 0 < n := hN.trans_le hn
  have herr (L : LatinArray n) :
      dist (standardMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) < rho/4 := herror n hnE L
  have hsubL : latinonEventLatinFamily (hV.trans_le hnV) (T ⁻¹' Metric.ball z sigma) ⊆
      standardMatrixPatternBoxFamily P z (rho/2) n := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (standardMatrixPatternProfile P L) z ≤ rho/2
    have hb : dist (T (latinArrayToLatinonMeasure hnp L)) z < sigma := hball
    have ht := dist_triangle (standardMatrixPatternProfile P L) (T (latinArrayToLatinonMeasure hnp L)) z
    have he := herr L
    linarith
  have hsubU : standardMatrixPatternBoxFamily P z (rho/2) n ⊆
      latinonEventLatinFamily (hU.trans_le hnU) (T ⁻¹' Metric.ball z rho) := by
    intro L hL
    obtain ⟨hAll,hball⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z < rho
    have hb : dist (standardMatrixPatternProfile P L) z ≤ rho/2 := hball
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (standardMatrixPatternProfile P L) < rho/4 := by
      rw [dist_comm]
      exact herr L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (standardMatrixPatternProfile P L) z
    linarith
  exact ⟨((hlower n hnV).1).trans (Nat.cast_le.mpr (Finset.card_le_card hsubL)),
    (Nat.cast_le.mpr (Finset.card_le_card hsubU)).trans ((hupper n hnU).2)⟩

theorem infinite_rate_standard_pattern_count_upper {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hinfinite : latinonContractedRate (latinonPatternProfile P) z=⊤)
    (r t eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      ((standardMatrixPatternBoxFamily P z rho n).card : ℝ) ≤
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
  obtain ⟨E,hE,herror⟩ := standard_pattern_profile_uniform_error P rho hrho
  let N := max U E
  refine ⟨rho,hrho,min_le_left _ _,N,hU.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnU : U ≤ n := (le_max_left _ _).trans hn
  have hnE : E ≤ n := (le_max_right _ _).trans hn
  have hnp : 0 < n := hU.trans_le hnU
  have hsub : standardMatrixPatternBoxFamily P z rho n ⊆
      latinonEventLatinFamily hnp (T ⁻¹' Metric.closedBall z (delta/2)) := by
    intro L hL
    obtain ⟨hAll,hb⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_filter.mpr
    refine ⟨hAll,?_⟩
    change dist (T (latinArrayToLatinonMeasure hnp L)) z ≤ delta/2
    have hdist : dist (standardMatrixPatternProfile P L) z ≤ rho := hb
    have he : dist (T (latinArrayToLatinonMeasure hnp L)) (standardMatrixPatternProfile P L) < rho := by
      rw [dist_comm]
      exact herror n hnE L
    have ht := dist_triangle (T (latinArrayToLatinonMeasure hnp L)) (standardMatrixPatternProfile P L) z
    have hrhod : rho ≤ delta/4 := min_le_right _ _
    linarith
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hupper n hnU)

end LatinonEntropy

#print axioms LatinonEntropy.mem_standardMatrixPatternBoxFamily_iff
#print axioms LatinonEntropy.finite_rate_standard_pattern_entropy_count
#print axioms LatinonEntropy.infinite_rate_standard_pattern_count_upper
