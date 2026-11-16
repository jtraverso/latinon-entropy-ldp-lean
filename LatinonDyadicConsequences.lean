module

public import LatinonDyadicGridKL
public import LatinonGridRateLocal
public import LatinSquareNormalization

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory InformationTheory Filter Topology Finset
open scoped Classical ENNReal unitInterval

theorem exists_dyadic_grid_divergence_gt_of_ac (W : LatinonMeasure)
    (hac : W.measure ≪ uniformLatinonMeasure.measure) (t : ℝ)
    (ht : ENNReal.ofReal t < latinonRate W) :
    ∃ k, t < -latinonGridTableEntropy W (dyadicGridSize k) := by
  rw [latinon_rate_eq_iSup_dyadic_of_ac W hac] at ht
  obtain ⟨k,hk⟩ := lt_iSup_iff.mp ht
  exact ⟨k,(ENNReal.ofReal_lt_ofReal_iff'.mp hk).1⟩

/-- Neighborhoods here contain every Latinon, not only absolutely
continuous ones. Absolute continuity is required only at the centre. -/
theorem latinon_rate_lowerSemicontinuousAt_of_ac (W : LatinonMeasure)
    (hac : W.measure ≪ uniformLatinonMeasure.measure) :
    LowerSemicontinuousAt latinonRate W := by
  intro y hy
  rw [latinon_rate_eq_iSup_dyadic_of_ac W hac] at hy
  obtain ⟨k,hk⟩ := lt_iSup_iff.mp hy
  have hr := ENNReal.toReal_lt_of_lt_ofReal hk
  let E := latinonGridTableEntropy W (dyadicGridSize k)
  let eta := (-E-y.toReal)/2
  have heta : 0 < eta := by dsimp only [eta,E]; linarith only [hr]
  obtain ⟨delta,hd,hlocal⟩ := exists_latinon_grid_rate_neighborhood W (dyadicGridSize_pos k) eta heta
  apply Filter.mem_of_superset (Metric.ball_mem_nhds W hd)
  intro V hV
  apply lt_of_lt_of_le _ (hlocal V hV)
  apply (ENNReal.lt_ofReal_iff_toReal_lt hk.ne_top).mpr
  dsimp only [eta,E]
  linarith only [hr]

/-- A rate threshold strictly below the actual KL gives a local upper
count with that exponent, uniformly over every finite family in the ball. -/
theorem exists_latinon_local_upper_below_rate_of_ac (W : LatinonMeasure)
    (hac : W.measure ≪ uniformLatinonMeasure.measure) (t : ℝ)
    (ht : ENNReal.ofReal t < latinonRate W) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n) (S : Finset (LatinArray n)),
      (∀ L ∈ S, latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*(Real.log (n : ℝ)-2-t)) := by
  obtain ⟨k,hk⟩ := exists_dyadic_grid_divergence_gt_of_ac W hac t ht
  let m := dyadicGridSize k
  have hm : 0 < m := dyadicGridSize_pos k
  let E := latinonGridTableEntropy W m
  have heta : 0 < -t-E := by dsimp only [E,m]; linarith only [hk]
  have hpos : ∀ i : Fin m, 0 < (volume : Measure I).real ((lebesgueGridPartition m hm).cell i) := by
    intro i
    change 0 < (volume : Measure I).real (lebesgueGridCell i)
    rw [lebesgueGridCell_mass hm]
    exact div_pos zero_lt_one (Nat.cast_pos.mpr hm)
  obtain ⟨delta,hd,N,hN,hcount⟩ := exists_latinon_partition_local_upper W
    (lebesgueGridPartition m hm) (lebesgueGridPartition m hm)
    (uniformSymbolPartition m hm) hpos hpos (-t-E) heta
  refine ⟨delta,hd,N,hN,?_⟩
  intro n hn S hS
  have hc := hcount n hn S hS
  rw [latinon_uniform_partition_entropy_eq_grid W hm] at hc
  have heq : Real.log (n : ℝ)-2+latinonGridTableEntropy W m+(-t-E) =
      Real.log (n : ℝ)-2-t := by dsimp only [E]; ring
  rwa [heq] at hc

/-- The sharp local count at every finite-rate centre. The KL value is
converted to a real only under its explicit finiteness hypothesis. -/
theorem exists_finite_rate_latinon_local_upper (W : LatinonMeasure)
    (hfinite : latinonRate W ≠ ⊤) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ (N : ℕ) (hN : 0 < N),
      ∀ (n : ℕ) (hn : N ≤ n) (S : Finset (LatinArray n)),
      (∀ L ∈ S, latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta) →
      (S.card : ℝ) ≤ Real.exp ((n : ℝ)^2*
        (Real.log (n : ℝ)-2-(latinonRate W).toReal+eta)) := by
  let R := (latinonRate W).toReal
  by_cases hsmall : R < eta
  · obtain ⟨N,hN,hcount⟩ := exists_total_latin_count_upper (eta-R) (sub_pos.mpr hsmall)
    refine ⟨1,zero_lt_one,N,hN,?_⟩
    intro n hn S _
    have hc := hcount n hn S
    have heq : Real.log (n : ℝ)-2+(eta-R) = Real.log (n : ℝ)-2-(latinonRate W).toReal+eta := by
      dsimp only [R]
      ring
    rwa [heq] at hc
  · have hac : W.measure ≪ uniformLatinonMeasure.measure :=
      (klDiv_ne_top_iff.mp hfinite).1
    have ht : ENNReal.ofReal (R-eta) < latinonRate W := by
      apply (ENNReal.ofReal_lt_iff_lt_toReal (sub_nonneg.mpr (le_of_not_gt hsmall)) hfinite).mpr
      dsimp only [R]
      linarith only [heta]
    obtain ⟨delta,hd,N,hN,hcount⟩ := exists_latinon_local_upper_below_rate_of_ac W hac (R-eta) ht
    refine ⟨delta,hd,N,hN,?_⟩
    intro n hn S hS
    have hc := hcount n hn S hS
    have heq : Real.log (n : ℝ)-2-(R-eta) = Real.log (n : ℝ)-2-(latinonRate W).toReal+eta := by
      dsimp only [R]
      ring
    rwa [heq] at hc

end LatinonEntropy

#print axioms LatinonEntropy.exists_dyadic_grid_divergence_gt_of_ac
#print axioms LatinonEntropy.latinon_rate_lowerSemicontinuousAt_of_ac
#print axioms LatinonEntropy.exists_latinon_local_upper_below_rate_of_ac
#print axioms LatinonEntropy.exists_finite_rate_latinon_local_upper
