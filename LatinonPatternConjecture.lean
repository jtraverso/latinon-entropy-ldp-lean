module

public import LatinonStandardPatternEntropy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical

/-- The finite-cost pattern counting formula in normalized logarithmic
form,with entropy convention Ent=-KL and binomial finite densities. -/
theorem finite_rate_standard_pattern_log_count {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hfinite : latinonContractedRate (latinonPatternProfile P) z ≠ ⊤)
    (r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n),
      0 < (standardMatrixPatternBoxFamily P z rho n).card ∧
      |Real.log ((standardMatrixPatternBoxFamily P z rho n).card : ℝ)/(n : ℝ)^2-
        (Real.log (n : ℝ)-2)+(latinonContractedRate (latinonPatternProfile P) z).toReal| ≤ eta := by
  obtain ⟨rho,hrho,hrhor,N,hN,hcount⟩ :=
    finite_rate_standard_pattern_entropy_count P z hfinite r eta hr heta
  refine ⟨rho,hrho,hrhor,N,hN,?_⟩
  intro n hn
  obtain ⟨hlo,hhi⟩ := hcount n hn
  have hpos : (0 : ℝ) < (standardMatrixPatternBoxFamily P z rho n).card :=
    (Real.exp_pos _).trans_le hlo
  have hnsq : (0 : ℝ) < (n : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (hN.trans_le hn))
  have hloLog := Real.log_le_log (Real.exp_pos _) hlo
  have hhiLog := Real.log_le_log hpos hhi
  rw [Real.log_exp] at hloLog hhiLog
  have hloDiv : Real.log (n : ℝ)-2-(latinonContractedRate (latinonPatternProfile P) z).toReal-eta ≤
      Real.log ((standardMatrixPatternBoxFamily P z rho n).card : ℝ)/(n : ℝ)^2 :=
    (le_div_iff₀ hnsq).mpr (by nlinarith only [hloLog])
  have hhiDiv : Real.log ((standardMatrixPatternBoxFamily P z rho n).card : ℝ)/(n : ℝ)^2 ≤
      Real.log (n : ℝ)-2-(latinonContractedRate (latinonPatternProfile P) z).toReal+eta :=
    (div_le_iff₀ hnsq).mpr (by nlinarith only [hhiLog])
  exact ⟨Nat.cast_pos.mp hpos,abs_le.mpr ⟨by linarith only [hloDiv],by linarith only [hhiDiv]⟩⟩

/-- An infeasible profile has an eventually EMPTY finite neighborhood,
using compactness of the actual continuous pattern image. -/
theorem empty_standard_pattern_fiber_eventually_zero {J : Type*} [Fintype J] {k l : J → ℕ}
    (P : ∀ j, LatinOrderPattern (k j) (l j)) (z : J → ℝ)
    (hempty : ¬∃ W : LatinonMeasure, latinonPatternProfile P W=z)
    (r : ℝ) (hr : 0 < r) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ r ∧ ∃ (N : ℕ) (_hN : 0 < N),
      ∀ (n : ℕ) (_hn : N ≤ n), (standardMatrixPatternBoxFamily P z rho n).card=0 := by
  let T := latinonPatternProfile P
  have hclosed : IsClosed (Set.range T) := (isCompact_range (continuous_latinonPatternProfile P)).isClosed
  have hz : z ∈ (Set.range T)ᶜ := hempty
  obtain ⟨delta,hdelta,hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hz
  let rho := min r (delta/4)
  have hrho : 0 < rho := lt_min hr (by positivity)
  obtain ⟨N,hN,herror⟩ := standard_pattern_profile_uniform_error P rho hrho
  refine ⟨rho,hrho,min_le_left _ _,N,hN,?_⟩
  intro n hn
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro L hL
  have hb : dist (standardMatrixPatternProfile P L) z ≤ rho := (Finset.mem_filter.mp hL).2
  have he : dist (T (latinArrayToLatinonMeasure (hN.trans_le hn) L)) (standardMatrixPatternProfile P L) < rho := by
    rw [dist_comm]
    exact herror n hn L
  have ht := dist_triangle (T (latinArrayToLatinonMeasure (hN.trans_le hn) L)) (standardMatrixPatternProfile P L) z
  have hrhod : rho ≤ delta/4 := min_le_right _ _
  have hin : T (latinArrayToLatinonMeasure (hN.trans_le hn) L) ∈ Metric.ball z delta := by
    change dist _ z < delta
    linarith only [ht,he,hb,hrhod,hdelta]
  exact (hball hin) ⟨latinArrayToLatinonMeasure (hN.trans_le hn) L,rfl⟩

end LatinonEntropy

#print axioms LatinonEntropy.finite_rate_standard_pattern_log_count
#print axioms LatinonEntropy.empty_standard_pattern_fiber_eventually_zero
