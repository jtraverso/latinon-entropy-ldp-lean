module

public import LatinonRawCutCompleteness

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonMeasure_eq_of_measure_order_eq {W V : LatinonMeasure}
    (hm : W.measure=V.measure) (ho : W.order=V.order) : W=V := by
  cases W
  cases V
  cases hm
  cases ho
  rfl

/-- A common relabeling acts on actual single-order Latinons. -/
def synchronousRelabel (W : LatinonMeasure) (e : LatinonRelabel) : LatinonMeasure where
  measure := relabelLatinonMeasure W.measure e e
  order := W.order ∘ e
  order_preserving := W.order_preserving.comp e.preserves
  xy_uniform := relabelLatinonMeasure_xy W e e
  xz_uniform := relabelLatinonMeasure_xz W e e
  yz_uniform := relabelLatinonMeasure_yz W e e

theorem synchronousRelabel_refl (W : LatinonMeasure) :
    synchronousRelabel W LatinonRelabel.refl=W := by
  apply latinonMeasure_eq_of_measure_order_eq
  · exact relabelLatinonMeasure_refl W.measure
  · rfl

theorem synchronousRelabel_comp (W : LatinonMeasure) (e g : LatinonRelabel) :
    synchronousRelabel (synchronousRelabel W g) e=synchronousRelabel W (e.trans g) := by
  apply latinonMeasure_eq_of_measure_order_eq
  · exact relabelLatinonMeasure_comp W.measure e e g g
  · rfl

theorem synchronousRelabel_inverse (W : LatinonMeasure) (e : LatinonRelabel) :
    synchronousRelabel (synchronousRelabel W e) e.symm=W := by
  apply latinonMeasure_eq_of_measure_order_eq
  · exact relabelLatinonMeasure_inverse W.measure e e
  · exact relabel_comp_inverse_cancel W.order e

theorem rawCutCost_synchronous_invariant (W V : LatinonMeasure) (e : LatinonRelabel) :
    latinonRawCutCost (synchronousRelabel W e) (synchronousRelabel V e)=latinonRawCutCost W V := by
  change 2*orderCut (W.order ∘ e) (V.order ∘ e)+
    measureCut (relabelLatinonMeasure W.measure e e) (relabelLatinonMeasure V.measure e e)=
      2*orderCut W.order V.order+measureCut W.measure V.measure
  rw [orderCut_comp_invariant W.order V.order W.order_preserving.measurable
    V.order_preserving.measurable e,measureCut_relabel_invariant]

theorem rawCutCost_synchronous_eq_alignmentCost (W V : LatinonMeasure) (e : LatinonRelabel) :
    latinonRawCutCost W (synchronousRelabel V e)=latinonAlignmentCost W V e e := by
  change 2*orderCut W.order (V.order ∘ e)+measureCut W.measure (relabelLatinonMeasure V.measure e e)=
    orderCut W.order (V.order ∘ e)+orderCut W.order (V.order ∘ e)+
      measureCut W.measure (relabelLatinonMeasure V.measure e e)
  ring

theorem synchronousRelabel_full_distance_zero (W : LatinonMeasure) (e : LatinonRelabel) :
    latinonCutDistance (synchronousRelabel W e) W=0 := by
  have hc : latinonAlignmentCost (synchronousRelabel W e) W e e=0 := by
    change orderCut (W.order ∘ e) (W.order ∘ e)+orderCut (W.order ∘ e) (W.order ∘ e)+
      measureCut (relabelLatinonMeasure W.measure e e) (relabelLatinonMeasure W.measure e e)=0
    rw [orderCut_self,measureCut_self]
    norm_num
  exact le_antisymm ((latinonCutDistance_le_cost _ _ e e).trans_eq hc)
    (latinonCutDistance_nonneg _ _)

end LatinonEntropy

#print axioms LatinonEntropy.latinonMeasure_eq_of_measure_order_eq
#print axioms LatinonEntropy.synchronousRelabel
#print axioms LatinonEntropy.synchronousRelabel_refl
#print axioms LatinonEntropy.synchronousRelabel_comp
#print axioms LatinonEntropy.synchronousRelabel_inverse
#print axioms LatinonEntropy.rawCutCost_synchronous_invariant
#print axioms LatinonEntropy.rawCutCost_synchronous_eq_alignmentCost
#print axioms LatinonEntropy.synchronousRelabel_full_distance_zero
