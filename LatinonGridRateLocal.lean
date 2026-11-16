module

public import LatinonGridKL

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval ENNReal

/-- Every fixed grid gives a local lower bound for the ACTUAL KL rate in
the full Latinon pseudometric. No alignment or entropy bound is assumed. -/
theorem exists_latinon_grid_rate_neighborhood (W : LatinonMeasure) {n : ℕ}
    (hn : 0 < n) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ V : LatinonMeasure, V ∈ Metric.ball W delta →
      ENNReal.ofReal (-latinonGridTableEntropy W n-eta) ≤ latinonRate V := by
  let v : GridBoxIndex n → ℝ := fun b => uniformLatinonMeasure.measure.real (latinonGridBox b)
  let t : GridBoxIndex n → ℝ := fun b => W.measure.real (latinonGridBox b)
  have hv : ∀ b, 0 < v b := by
    intro b
    dsimp only [v]
    rw [uniform_latinon_grid_box_mass hn]
    exact pow_pos (div_pos zero_lt_one (Nat.cast_pos.mpr hn)) 3
  obtain ⟨delta,hd,hcont⟩ := finite_table_entropy_local_upper v t hv eta heta
  refine ⟨delta,hd,?_⟩
  intro V hV
  obtain ⟨e,f,hbox⟩ := exists_box_alignment_of_mem_ball W V delta hV
  -- Only this auxiliary object's measure is used. The actual metric
  -- alignment was extracted from W,V above,including their order terms.
  let V' : LatinonMeasure := {
    measure := relabelLatinonMeasure V.measure e f
    order := id
    order_preserving := MeasurePreserving.id volume
    xy_uniform := relabelLatinonMeasure_xy V e f
    xz_uniform := relabelLatinonMeasure_xz V e f
    yz_uniform := relabelLatinonMeasure_yz V e f
  }
  have ht : ∀ b : GridBoxIndex n, |V'.measure.real (latinonGridBox b)-t b| < delta := by
    intro b
    let box := intervalLatinonBox (lebesgueGridCell b.1.1) (lebesgueGridCell b.1.2)
      (lebesgueGridCell_measurable b.1.1) (lebesgueGridCell_measurable b.1.2)
      (symbolGridLower b.2) (symbolGridUpper b.2)
    have hb := hbox box
    change |t b-V'.measure.real (latinonGridBox b)| < delta at hb
    rwa [abs_sub_comm] at hb
  have he := hcont v (fun b => V'.measure.real (latinonGridBox b))
    (fun b => by rw [sub_self,abs_zero]; exact hd) ht
  change latinonGridTableEntropy V' n ≤ latinonGridTableEntropy W n+eta at he
  have hrate : latinonRate V' = latinonRate V := latinon_measure_rate_relabel V e f
  have hg := latinon_grid_table_divergence_le V' hn
  rw [hrate] at hg
  exact (ENNReal.ofReal_le_ofReal (by linarith only [he])).trans hg

end LatinonEntropy

#print axioms LatinonEntropy.exists_latinon_grid_rate_neighborhood
#print axioms LatinonEntropy.latinonGridBox_measurable
#print axioms LatinonEntropy.latinonGridBox_disjoint
#print axioms LatinonEntropy.latinonGridBox_cover
#print axioms LatinonEntropy.uniform_latinon_grid_box_mass
#print axioms LatinonEntropy.latinon_grid_table_divergence_le
#print axioms LatinonEntropy.latinon_grid_table_entropy_eq_density
#print axioms LatinonEntropy.latinon_grid_density_divergence_le
#print axioms LatinonEntropy.latinon_entropy_le_grid_density_entropy
#print axioms LatinonEntropy.uniformSymbolPartition_interval
#print axioms LatinonEntropy.uniformSymbolPartition_width
#print axioms LatinonEntropy.latinon_uniform_partition_entropy_eq_grid
#print axioms LatinonEntropy.finite_measure_ac_of_positive_reference
#print axioms LatinonEntropy.finite_rnDeriv_eq_ratio
#print axioms LatinonEntropy.finite_measure_real_univ
#print axioms LatinonEntropy.finite_kl_ne_top
#print axioms LatinonEntropy.finite_kl_toReal_eq_sum
#print axioms LatinonEntropy.finite_kl_eq_ofReal_sum
#print axioms LatinonEntropy.finite_probability_kl_eq_neg_table
#print axioms LatinonEntropy.finiteCellIndex_of_mem
#print axioms LatinonEntropy.finiteCellIndex_eq_iff_of_covered
#print axioms LatinonEntropy.finiteCellIndex_fiber
#print axioms LatinonEntropy.finiteCellIndex_measurable
#print axioms LatinonEntropy.finiteCellIndex_map_cell
#print axioms LatinonEntropy.finite_cell_table_kl_le
