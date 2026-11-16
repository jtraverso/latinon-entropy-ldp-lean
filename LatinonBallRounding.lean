module

public import LatinonPseudometric
public import RelabelledFiniteLatinon

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

/-- Actual pseudometric-ball membership yields a rounded block window at
the target Latinon. The uniform threshold precedes all measurable data. -/
theorem exists_uniform_metric_ball_rounding (W : LatinonMeasure) {t : ℕ}
    (P : SymbolIntervalPartition t) (r s : ℕ) (tau : ℝ) (htau : 0 < tau) (M : ℕ) :
    ∃ (N : ℕ) (hN : 0 < N), ∀ (n : ℕ) (hn : N ≤ n),
      ∀ (A : MeasurableFinitePartition (volume : Measure I) r)
        (B : MeasurableFinitePartition (volume : Measure I) s)
        (L : LatinArray n) (delta : ℝ),
      latinArrayToLatinonMeasure (hN.trans_le hn) L ∈ Metric.ball W delta →
      ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
            W.measure.real ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ
              unitSymbolInterval (P.left z.2) (P.right z.2))| < tau+delta) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-volume.real (A.cell a)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-volume.real (B.cell b)| < tau) ∧
        (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ)) := by
  obtain ⟨N,hN,hround⟩ := exists_uniform_relabelled_measure_rounding P r s tau htau M
  refine ⟨N,hN,?_⟩
  intro n hn A B L delta hball
  obtain ⟨e,f,hcut⟩ := exists_box_alignment_of_mem_ball W
    (latinArrayToLatinonMeasure (hN.trans_le hn) L) delta hball
  obtain ⟨row,col,hb,hr,hc,hsize⟩ := hround n hn A B e f L
  refine ⟨row,col,?_,hr,hc,hsize⟩
  intro z
  let box := intervalLatinonBox (A.cell z.1.1) (B.cell z.1.2)
    (A.measurable z.1.1) (B.measurable z.1.2) (P.left z.2) (P.right z.2)
  have hclose := hcut box
  change |W.measure.real ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2))-
      (relabelLatinonMeasure (finiteLatinMeasure L) e f).real
        ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2))| < delta at hclose
  have hreverse := hclose
  rw [abs_sub_comm] at hreverse
  have htriangle := abs_sub_le (latinBlockObservable row col (P.color n) z L/(n : ℝ)^2)
    ((relabelLatinonMeasure (finiteLatinMeasure L) e f).real
      ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2)))
    (W.measure.real ((A.cell z.1.1 ×ˢ B.cell z.1.2) ×ˢ unitSymbolInterval (P.left z.2) (P.right z.2)))
  have hbz := hb z
  linarith only [htriangle,hbz,hreverse]

example : uniformLatinonMeasure ∈ Metric.ball uniformLatinonMeasure 1 := by
  rw [mem_latinon_ball_iff,latinonCutDistance_self]
  norm_num

end LatinonEntropy

#print axioms LatinonEntropy.exists_uniform_metric_ball_rounding
#print axioms LatinonEntropy.LatinonRelabel.symm
#print axioms LatinonEntropy.LatinonRelabel.trans
#print axioms LatinonEntropy.LatinonRelabel.image_eq_inverse_preimage
#print axioms LatinonEntropy.LatinonRelabel.image_measurable
#print axioms LatinonEntropy.LatinonRelabel.image_measure
#print axioms LatinonEntropy.LatinonRelabel.inverse_image_inter_mass
#print axioms LatinonEntropy.inverseCoordinateRelabel_measurable
#print axioms LatinonEntropy.relabelLatinonMeasure_box
#print axioms LatinonEntropy.relabelLatinonMeasure_real_box
#print axioms LatinonEntropy.relabelLatinonMeasure_xy
#print axioms LatinonEntropy.relabelLatinonMeasure_xz
#print axioms LatinonEntropy.relabelLatinonMeasure_yz
#print axioms LatinonEntropy.relabelLatinonMeasure_refl
#print axioms LatinonEntropy.relabelled_finite_interval_integral
#print axioms LatinonEntropy.relabelled_finite_block_table
#print axioms LatinonEntropy.exists_uniform_relabelled_measure_rounding
#print axioms LatinonEntropy.intervalLatinonBox
#print axioms LatinonEntropy.measureCut_test_le
#print axioms LatinonEntropy.measureCut_nonneg
#print axioms LatinonEntropy.measureCut_le_one
#print axioms LatinonEntropy.measureCut_self
#print axioms LatinonEntropy.measureCut_symm
#print axioms LatinonEntropy.measureCut_triangle
#print axioms LatinonEntropy.orderCut_test_le
#print axioms LatinonEntropy.orderCut_nonneg
#print axioms LatinonEntropy.orderCut_le_one
#print axioms LatinonEntropy.orderCut_self
#print axioms LatinonEntropy.orderCut_symm
#print axioms LatinonEntropy.orderCut_triangle
#print axioms LatinonEntropy.orderBox_eq_integral
#print axioms LatinonEntropy.latinonAlignmentCost_nonneg
#print axioms LatinonEntropy.latinonAlignmentCost_le_three
#print axioms LatinonEntropy.latinonCutDistance_nonneg
#print axioms LatinonEntropy.latinonCutDistance_le_cost
#print axioms LatinonEntropy.latinonCutDistance_le_three
#print axioms LatinonEntropy.latinonCutDistance_self
#print axioms LatinonEntropy.exists_alignmentCost_lt
#print axioms LatinonEntropy.exists_alignment_of_cutDistance_lt
#print axioms LatinonEntropy.exists_box_alignment_of_cutDistance_lt
#print axioms LatinonEntropy.relabelLatinonMeasure_comp
#print axioms LatinonEntropy.relabelLatinonMeasure_inverse
#print axioms LatinonEntropy.measureCut_relabel_invariant
#print axioms LatinonEntropy.orderBox_comp
#print axioms LatinonEntropy.orderCut_comp_invariant
#print axioms LatinonEntropy.orderCut_inverse_eq
#print axioms LatinonEntropy.measureCut_inverse_eq
#print axioms LatinonEntropy.latinonAlignmentCost_inverse
#print axioms LatinonEntropy.latinonCutDistance_symm
#print axioms LatinonEntropy.latinonAlignmentCost_triangle
#print axioms LatinonEntropy.latinonCutDistance_triangle
#print axioms LatinonEntropy.latinonMeasure_dist_eq
#print axioms LatinonEntropy.mem_latinon_ball_iff
#print axioms LatinonEntropy.exists_box_alignment_of_mem_ball
