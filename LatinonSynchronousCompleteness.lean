module

public import LatinonSynchronousDistance
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

/-- Used locally for the geometric-series Cauchy criterion; this does not
replace the original Latinon pseudometric instance. -/
@[instance_reducible] def rawLatinonPseudoMetric : PseudoMetricSpace LatinonMeasure where
  dist := latinonRawCutCost
  dist_self W := by simp only [latinonRawCutCost,orderCut_self,measureCut_self,mul_zero,add_zero]
  dist_comm W V := by
    unfold latinonRawCutCost
    rw [orderCut_symm W.order V.order,measureCut_symm W.measure V.measure]
  dist_triangle := latinonRawCutCost_triangle

/-- A fast Cauchy sequence can be aligned successively by actual common MP
bijections. Its aligned raw-cut limit gives a limit in the synchronous
quotient pseudometric. No finite-cover or compactness hypothesis is used. -/
theorem synchronousLatinon_complete : CompleteSpace SynchronousLatinon := by
  apply Metric.complete_of_convergent_controlled_sequences (fun n => (1/2 : ℝ)^n)
    (fun n => pow_pos (by norm_num) n)
  intro u hcontrol
  choose e he using (fun n => exists_synchronousCost_lt (u n).value (u (n+1)).value
    ((1/2 : ℝ)^n) (hcontrol n n (n+1) le_rfl (Nat.le_succ n)))
  let a : ℕ → LatinonRelabel := Nat.rec LatinonRelabel.refl (fun n acc => acc.trans (e n))
  have ha (n : ℕ) : a (n+1)=(a n).trans (e n) := rfl
  let v : ℕ → LatinonMeasure := fun n => synchronousRelabel (u n).value (a n)
  have hstep (n : ℕ) : latinonRawCutCost (v n) (v (n+1)) ≤ (1/2 : ℝ)^n := by
    change latinonRawCutCost (synchronousRelabel (u n).value (a n))
      (synchronousRelabel (u (n+1)).value (a (n+1))) ≤ (1/2 : ℝ)^n
    rw [ha n,← synchronousRelabel_comp (u (n+1)).value (a n) (e n),
      rawCutCost_synchronous_invariant,rawCutCost_synchronous_eq_alignmentCost]
    exact (he n).le
  have hraw : ∃ V : LatinonMeasure,
      Tendsto (fun n => latinonRawCutCost (v n) V) atTop (𝓝 0) := by
    let : PseudoMetricSpace LatinonMeasure := rawLatinonPseudoMetric
    have hC : CauchySeq v := cauchySeq_of_le_geometric (1/2 : ℝ) 1 (by norm_num)
      (fun n => by
        change latinonRawCutCost (v n) (v (n+1)) ≤ 1*(1/2 : ℝ)^n
        rw [one_mul]
        exact hstep n)
    apply exists_raw_latinon_cut_limit v
    · intro eps heps
      obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hC eps heps
      refine ⟨N,?_⟩
      intro m hm n hn
      have hc := hN m hm n hn
      change latinonRawCutCost (v m) (v n) < eps at hc
      have hp := measureCut_nonneg (v m).measure (v n).measure
      have ho := orderCut_nonneg (v m).order (v n).order
      unfold latinonRawCutCost at hc
      linarith only [hc,hp,ho]
    · intro eps heps
      obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hC eps heps
      refine ⟨N,?_⟩
      intro m hm n hn
      have hc := hN m hm n hn
      change latinonRawCutCost (v m) (v n) < eps at hc
      have ho := orderCut_nonneg (v m).order (v n).order
      unfold latinonRawCutCost at hc
      linarith only [hc,ho]
  obtain ⟨V,hV⟩ := hraw
  refine ⟨⟨V⟩,tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  apply squeeze_zero (fun n => dist_nonneg) _ hV
  intro n
  change synchronousCutDistance (u n).value V ≤ latinonRawCutCost (v n) V
  have hz : synchronousCutDistance (u n).value (v n)=0 := by
    rw [synchronousCutDistance_symm]
    exact synchronousCutDistance_relabel_zero (u n).value (a n)
  calc
    synchronousCutDistance (u n).value V ≤
        synchronousCutDistance (u n).value (v n)+synchronousCutDistance (v n) V :=
      synchronousCutDistance_triangle _ _ _
    _ ≤ latinonRawCutCost (v n) V := by
      rw [hz,zero_add]
      exact synchronousCutDistance_le_rawCost _ _

instance : CompleteSpace SynchronousLatinon := synchronousLatinon_complete

end LatinonEntropy

#print axioms LatinonEntropy.rawLatinonPseudoMetric
#print axioms LatinonEntropy.synchronousLatinon_complete
