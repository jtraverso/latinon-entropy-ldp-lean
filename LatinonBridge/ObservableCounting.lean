module

public import LatinonBridge.Contraction

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical ENNReal

/-- Closed observable restrictions count actual Latin squares, with the
second-order normalization and the contracted entropy cost. -/
theorem closed_observable_latin_count_upper {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    (F : Set Y) (hF : IsClosed F) (t : ℝ)
    (ht : ∀ z ∈ F, ENNReal.ofReal t ≤ latinonContractedRate T z)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ((latinonEventLatinFamily (hN.trans_le hn) (T ⁻¹' F)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eps)) := by
  obtain ⟨A,hA,hprob⟩ := contracted_closed_uniform_latinon_upper T hT F hF t ht (eps/2) (half_pos heps)
  obtain ⟨B,hB,htotal⟩ := total_latin_square_count_normalization (eps/2) (half_pos heps)
  refine ⟨max A B,hA.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnA : A ≤ n := (le_max_left _ _).trans hn
  have hnB : B ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := hA.trans_le hnA
  have hp := hprob n hnA
  rw [latinonObservableLaw_real_event T hT _ F hF.measurableSet,
    uniformLatinonLaw_real_event _ _ (hF.preimage hT).measurableSet] at hp
  have htotpos : 0 < ((allLatinSquares n).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (allLatinSquares_nonempty n hnpos))
  have hc := (div_le_iff₀ htotpos).mp hp
  calc
    _ ≤ Real.exp ((n : ℝ)^2*(-t+eps/2))*((allLatinSquares n).card : ℝ) := hc
    _ ≤ Real.exp ((n : ℝ)^2*(-t+eps/2))*
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2+eps/2)) :=
      mul_le_mul_of_nonneg_left (htotal n hnB).2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Open restrictions have the matching lower count whenever they contain
an observable value with finite contracted cost at most the threshold. -/
theorem open_observable_latin_count_lower {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (T : LatinonMeasure → Y) (hT : Continuous T)
    (G : Set Y) (hG : IsOpen G) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∃ z ∈ G, latinonContractedRate T z ≤ ENNReal.ofReal t)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t-eps)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (T ⁻¹' G)).card : ℝ) := by
  obtain ⟨A,hA,hprob⟩ := contracted_open_uniform_latinon_lower T hT G hG t ht0 ht (eps/2) (half_pos heps)
  obtain ⟨B,hB,htotal⟩ := total_latin_square_count_normalization (eps/2) (half_pos heps)
  refine ⟨max A B,hA.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hnA : A ≤ n := (le_max_left _ _).trans hn
  have hnB : B ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := hA.trans_le hnA
  have hp := hprob n hnA
  rw [latinonObservableLaw_real_event T hT _ G hG.measurableSet,
    uniformLatinonLaw_real_event _ _ (hG.preimage hT).measurableSet] at hp
  have htotpos : 0 < ((allLatinSquares n).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (allLatinSquares_nonempty n hnpos))
  have hc := (le_div_iff₀ htotpos).mp hp
  calc
    _ = Real.exp (-(n : ℝ)^2*(t+eps/2))*
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-eps/2)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(n : ℝ)^2*(t+eps/2))*((allLatinSquares n).card : ℝ) :=
      mul_le_mul_of_nonneg_left (htotal n hnB).1 (Real.exp_pos _).le
    _ ≤ _ := hc

def latinonDistanceProfile {k : ℕ} (centers : Fin k → LatinonMeasure)
    (W : LatinonMeasure) : Fin k → ℝ := fun i => dist W (centers i)

theorem continuous_latinonDistanceProfile {k : ℕ} (centers : Fin k → LatinonMeasure) :
    Continuous (latinonDistanceProfile centers) :=
  continuous_pi (fun _ => continuous_id.dist continuous_const)

theorem distance_profile_rate_sublevels_compact {k : ℕ} (centers : Fin k → LatinonMeasure)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) :
    IsCompact {z | latinonContractedRate (latinonDistanceProfile centers) z ≤ r} :=
  latinonContractedRate_sublevels_compact _ (continuous_latinonDistanceProfile centers) r hr

theorem closed_distance_profile_latin_count_upper {k : ℕ} (centers : Fin k → LatinonMeasure)
    (F : Set (Fin k → ℝ)) (hF : IsClosed F) (t : ℝ)
    (ht : ∀ z ∈ F, ENNReal.ofReal t ≤ latinonContractedRate (latinonDistanceProfile centers) z)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ((latinonEventLatinFamily (hN.trans_le hn) (latinonDistanceProfile centers ⁻¹' F)).card : ℝ) ≤
        Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t+eps)) :=
  closed_observable_latin_count_upper _ (continuous_latinonDistanceProfile centers) F hF t ht eps heps

theorem open_distance_profile_latin_count_lower {k : ℕ} (centers : Fin k → LatinonMeasure)
    (G : Set (Fin k → ℝ)) (hG : IsOpen G) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∃ z ∈ G, latinonContractedRate (latinonDistanceProfile centers) z ≤ ENNReal.ofReal t)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t-eps)) ≤
        ((latinonEventLatinFamily (hN.trans_le hn) (latinonDistanceProfile centers ⁻¹' G)).card : ℝ) :=
  open_observable_latin_count_lower _ (continuous_latinonDistanceProfile centers) G hG t ht0 ht eps heps

end LatinonEntropy

#print axioms LatinonEntropy.closed_observable_latin_count_upper
#print axioms LatinonEntropy.open_observable_latin_count_lower
#print axioms LatinonEntropy.continuous_latinonDistanceProfile
#print axioms LatinonEntropy.distance_profile_rate_sublevels_compact
#print axioms LatinonEntropy.closed_distance_profile_latin_count_upper
#print axioms LatinonEntropy.open_distance_profile_latin_count_lower
