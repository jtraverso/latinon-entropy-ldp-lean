module

public import LatinonCutDistance
public import LatinonCutInvariance
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem orderCut_inverse_eq (f g : I → I) (hf : Measurable f) (hg : Measurable g) (e : LatinonRelabel) :
    orderCut f (g ∘ e) = orderCut g (f ∘ e.symm) := by
  have h := orderCut_comp_invariant f (g ∘ e) hf (hg.comp e.measurable) e.symm
  rw [relabel_comp_inverse_cancel] at h
  exact h.symm.trans (orderCut_symm _ _)

theorem measureCut_inverse_eq (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (e f : LatinonRelabel) :
    measureCut mu (relabelLatinonMeasure nu e f) =
      measureCut nu (relabelLatinonMeasure mu e.symm f.symm) := by
  have h := measureCut_relabel_invariant mu (relabelLatinonMeasure nu e f) e.symm f.symm
  rw [relabelLatinonMeasure_inverse] at h
  exact h.symm.trans (measureCut_symm _ _)

theorem latinonAlignmentCost_inverse (W V : LatinonMeasure) (e f : LatinonRelabel) :
    latinonAlignmentCost W V e f = latinonAlignmentCost V W e.symm f.symm := by
  unfold latinonAlignmentCost
  rw [orderCut_inverse_eq W.order V.order W.order_preserving.measurable V.order_preserving.measurable e,
    orderCut_inverse_eq W.order V.order W.order_preserving.measurable V.order_preserving.measurable f,
    measureCut_inverse_eq]

theorem latinonCutDistance_le_reverse (W V : LatinonMeasure) :
    latinonCutDistance W V ≤ latinonCutDistance V W := by
  apply le_csInf (alignmentCost_range_nonempty V W)
  rintro _ ⟨p,rfl⟩
  exact (latinonCutDistance_le_cost W V p.1.symm p.2.symm).trans_eq
    (latinonAlignmentCost_inverse V W p.1 p.2).symm

theorem latinonCutDistance_symm (W V : LatinonMeasure) : latinonCutDistance W V = latinonCutDistance V W :=
  le_antisymm (latinonCutDistance_le_reverse W V) (latinonCutDistance_le_reverse V W)

theorem latinonAlignmentCost_triangle (W V U : LatinonMeasure) (e f g h : LatinonRelabel) :
    latinonAlignmentCost W U (e.trans g) (f.trans h) ≤
      latinonAlignmentCost W V e f+latinonAlignmentCost V U g h := by
  have hr := orderCut_triangle W.order (V.order ∘ e) ((U.order ∘ g) ∘ e)
  rw [orderCut_comp_invariant V.order (U.order ∘ g) V.order_preserving.measurable
    (U.order_preserving.measurable.comp g.measurable) e] at hr
  have hc := orderCut_triangle W.order (V.order ∘ f) ((U.order ∘ h) ∘ f)
  rw [orderCut_comp_invariant V.order (U.order ∘ h) V.order_preserving.measurable
    (U.order_preserving.measurable.comp h.measurable) f] at hc
  have hd := measureCut_triangle W.measure (relabelLatinonMeasure V.measure e f)
    (relabelLatinonMeasure (relabelLatinonMeasure U.measure g h) e f)
  rw [measureCut_relabel_invariant] at hd
  rw [relabelLatinonMeasure_comp] at hd
  change orderCut W.order (U.order ∘ (e.trans g)) ≤
    orderCut W.order (V.order ∘ e)+orderCut V.order (U.order ∘ g) at hr
  change orderCut W.order (U.order ∘ (f.trans h)) ≤
    orderCut W.order (V.order ∘ f)+orderCut V.order (U.order ∘ h) at hc
  unfold latinonAlignmentCost
  linarith only [hr,hc,hd]

theorem latinonCutDistance_triangle (W V U : LatinonMeasure) :
    latinonCutDistance W U ≤ latinonCutDistance W V+latinonCutDistance V U := by
  by_contra hn
  have hgt : latinonCutDistance W V+latinonCutDistance V U < latinonCutDistance W U := lt_of_not_ge hn
  let eps := (latinonCutDistance W U-(latinonCutDistance W V+latinonCutDistance V U))/3
  have heps : 0 < eps := div_pos (sub_pos.mpr hgt) (by norm_num)
  obtain ⟨e,f,h1⟩ := exists_alignmentCost_lt W V (latinonCutDistance W V+eps) (by linarith only [heps])
  obtain ⟨g,h,h2⟩ := exists_alignmentCost_lt V U (latinonCutDistance V U+eps) (by linarith only [heps])
  have ht := latinonAlignmentCost_triangle W V U e f g h
  have hl := latinonCutDistance_le_cost W U (e.trans g) (f.trans h)
  dsimp only [eps] at h1 h2
  linarith only [h1,h2,ht,hl,hgt]

/-- The actual topology is induced by the full cut pseudometric, including order. -/
instance : PseudoMetricSpace LatinonMeasure where
  dist := latinonCutDistance
  dist_self := latinonCutDistance_self
  dist_comm := latinonCutDistance_symm
  dist_triangle := latinonCutDistance_triangle

theorem latinonMeasure_dist_eq (W V : LatinonMeasure) : dist W V = latinonCutDistance W V := rfl

theorem mem_latinon_ball_iff (W V : LatinonMeasure) (delta : ℝ) :
    V ∈ Metric.ball W delta ↔ latinonCutDistance W V < delta := by
  change latinonCutDistance V W < delta ↔ latinonCutDistance W V < delta
  rw [latinonCutDistance_symm]

theorem exists_box_alignment_of_mem_ball (W V : LatinonMeasure) (delta : ℝ)
    (h : V ∈ Metric.ball W delta) :
    ∃ e f : LatinonRelabel, ∀ B : LatinonBox,
      |W.measure.real B.carrier-(relabelLatinonMeasure V.measure e f).real B.carrier| < delta :=
  exists_box_alignment_of_cutDistance_lt W V delta ((mem_latinon_ball_iff W V delta).mp h)

end LatinonEntropy

#print axioms LatinonEntropy.orderCut_inverse_eq
#print axioms LatinonEntropy.measureCut_inverse_eq
#print axioms LatinonEntropy.latinonAlignmentCost_inverse
#print axioms LatinonEntropy.latinonCutDistance_symm
#print axioms LatinonEntropy.latinonAlignmentCost_triangle
#print axioms LatinonEntropy.latinonCutDistance_triangle
#print axioms LatinonEntropy.latinonMeasure_dist_eq
#print axioms LatinonEntropy.mem_latinon_ball_iff
#print axioms LatinonEntropy.exists_box_alignment_of_mem_ball
