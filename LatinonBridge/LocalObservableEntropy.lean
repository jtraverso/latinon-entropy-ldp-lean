module

public import LatinonBridge.ObservableCounting

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

theorem finite_contracted_rate_local_floor {Y : Type*} [MetricSpace Y]
    (T : LatinonMeasure → Y) (hT : Continuous T) (z : Y)
    (hfinite : latinonContractedRate T z ≠ ⊤) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z', dist z' z ≤ delta →
      ENNReal.ofReal ((latinonContractedRate T z).toReal-eta) ≤ latinonContractedRate T z' := by
  let t := (latinonContractedRate T z).toReal-eta
  by_cases ht : t ≤ 0
  · refine ⟨1,by norm_num,?_⟩
    intro z' _
    change ENNReal.ofReal t ≤ _
    rw [ENNReal.ofReal_eq_zero.mpr ht]
    exact bot_le
  · have htpos : 0 < t := lt_of_not_ge ht
    have hstrict : ENNReal.ofReal t < latinonContractedRate T z := by
      rw [← ENNReal.ofReal_toReal hfinite]
      apply ENNReal.ofReal_lt_ofReal_iff'.mpr
      constructor
      · dsimp [t]
        linarith only [heta]
      · exact htpos.trans (by dsimp [t]; linarith only [heta])
    have hnhds := latinonContractedRate_lowerSemicontinuous T hT z (ENNReal.ofReal t) hstrict
    obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp hnhds
    refine ⟨delta/2,half_pos hdelta,?_⟩
    intro z' hz'
    apply le_of_lt
    apply hball
    change dist z' z < delta
    exact hz'.trans_lt (by linarith only [hdelta])

/-- Microcanonical entropy formula for any continuous metric-valued observable.
The radius can be chosen below any prescribed positive radius. -/
theorem finite_rate_observable_entropy_count {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    (z : Y) (hfinite : latinonContractedRate T z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonContractedRate T z).toReal-eta)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (T ⁻¹' Metric.ball z rho)).card : ℝ) ∧
      ((latinonEventLatinFamily (hN.trans_le hn) (T ⁻¹' Metric.ball z rho)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-(latinonContractedRate T z).toReal+eta)) := by
  obtain ⟨delta,hdelta,hfloor⟩ := finite_contracted_rate_local_floor T hT z hfinite (eta/2) (half_pos heta)
  let rho := min delta r
  have hrho : 0 < rho := lt_min hdelta hr
  have hclosedRate : ∀ z' ∈ Metric.closedBall z rho,
      ENNReal.ofReal ((latinonContractedRate T z).toReal-eta/2) ≤ latinonContractedRate T z' := by
    intro z' hz'
    exact hfloor z' (hz'.trans (min_le_left _ _))
  obtain ⟨A,hA,hupper⟩ := closed_observable_latin_count_upper T hT (Metric.closedBall z rho)
    Metric.isClosed_closedBall ((latinonContractedRate T z).toReal-eta/2) hclosedRate (eta/2) (half_pos heta)
  have hwitness : ∃ z' ∈ Metric.ball z rho,
      latinonContractedRate T z' ≤ ENNReal.ofReal (latinonContractedRate T z).toReal :=
    ⟨z,Metric.mem_ball_self hrho,by rw [ENNReal.ofReal_toReal hfinite]⟩
  obtain ⟨B,hB,hlower⟩ := open_observable_latin_count_lower T hT (Metric.ball z rho)
    Metric.isOpen_ball (latinonContractedRate T z).toReal ENNReal.toReal_nonneg hwitness eta heta
  refine ⟨rho,hrho,min_le_right _ _,max A B,hA.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnA : A ≤ n := (le_max_left _ _).trans hn
  have hnB : B ≤ n := (le_max_right _ _).trans hn
  refine ⟨hlower n hnB,?_⟩
  have hsub : latinonEventLatinFamily (hA.trans_le hnA) (T ⁻¹' Metric.ball z rho) ⊆
      latinonEventLatinFamily (hA.trans_le hnA) (T ⁻¹' Metric.closedBall z rho) := by
    intro L hL
    obtain ⟨hL,hball⟩ := Finset.mem_filter.mp hL
    exact Finset.mem_filter.mpr ⟨hL,Metric.ball_subset_closedBall hball⟩
  calc
    _ ≤ ((latinonEventLatinFamily (hA.trans_le hnA) (T ⁻¹' Metric.closedBall z rho)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        ((latinonContractedRate T z).toReal-eta/2)+eta/2)) := hupper n hnA
    _ = _ := by congr 1; ring

theorem finite_rate_distance_profile_entropy_count {k : ℕ} (centers : Fin k → LatinonMeasure)
    (z : Fin k → ℝ) (hfinite : latinonContractedRate (latinonDistanceProfile centers) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
        (latinonContractedRate (latinonDistanceProfile centers) z).toReal-eta)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (latinonDistanceProfile centers ⁻¹' Metric.ball z rho)).card : ℝ) ∧
      ((latinonEventLatinFamily (hN.trans_le hn) (latinonDistanceProfile centers ⁻¹' Metric.ball z rho)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-
          (latinonContractedRate (latinonDistanceProfile centers) z).toReal+eta)) :=
  finite_rate_observable_entropy_count _ (continuous_latinonDistanceProfile centers) z hfinite r eta hr heta

end LatinonEntropy

#print axioms LatinonEntropy.finite_contracted_rate_local_floor
#print axioms LatinonEntropy.finite_rate_observable_entropy_count
#print axioms LatinonEntropy.finite_rate_distance_profile_entropy_count
