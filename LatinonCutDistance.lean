module

public import LatinonCutNorms
public import LatinonMeasureAlignment

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Source formula (2): two order terms and the distribution cut norm,
over two actual measure-preserving measurable bijections. -/
def latinonAlignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) : ℝ :=
  orderCut W.order (V.order ∘ e)+orderCut W.order (V.order ∘ f)+
    measureCut W.measure (relabelLatinonMeasure V.measure e f)

def latinonCutDistance (W V : LatinonMeasure) : ℝ :=
  sInf (Set.range (fun p : LatinonRelabel × LatinonRelabel => latinonAlignmentCost W V p.1 p.2))

theorem latinonAlignmentCost_nonneg (W V : LatinonMeasure) (e f : LatinonRelabel) :
    0 ≤ latinonAlignmentCost W V e f :=
  add_nonneg (add_nonneg (orderCut_nonneg _ _) (orderCut_nonneg _ _)) (measureCut_nonneg _ _)

theorem latinonAlignmentCost_le_three (W V : LatinonMeasure) (e f : LatinonRelabel) :
    latinonAlignmentCost W V e f ≤ 3 := by
  unfold latinonAlignmentCost
  linarith only [orderCut_le_one W.order (V.order ∘ e),orderCut_le_one W.order (V.order ∘ f),
    measureCut_le_one W.measure (relabelLatinonMeasure V.measure e f)]

theorem measureCut_le_alignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) :
    measureCut W.measure (relabelLatinonMeasure V.measure e f) ≤ latinonAlignmentCost W V e f := by
  unfold latinonAlignmentCost
  linarith only [orderCut_nonneg W.order (V.order ∘ e),orderCut_nonneg W.order (V.order ∘ f)]

theorem row_orderCut_le_alignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) :
    orderCut W.order (V.order ∘ e) ≤ latinonAlignmentCost W V e f := by
  unfold latinonAlignmentCost
  linarith only [orderCut_nonneg W.order (V.order ∘ f),
    measureCut_nonneg W.measure (relabelLatinonMeasure V.measure e f)]

theorem col_orderCut_le_alignmentCost (W V : LatinonMeasure) (e f : LatinonRelabel) :
    orderCut W.order (V.order ∘ f) ≤ latinonAlignmentCost W V e f := by
  unfold latinonAlignmentCost
  linarith only [orderCut_nonneg W.order (V.order ∘ e),
    measureCut_nonneg W.measure (relabelLatinonMeasure V.measure e f)]

theorem alignmentCost_range_nonempty (W V : LatinonMeasure) :
    (Set.range (fun p : LatinonRelabel × LatinonRelabel => latinonAlignmentCost W V p.1 p.2)).Nonempty :=
  ⟨_,⟨(LatinonRelabel.refl,LatinonRelabel.refl),rfl⟩⟩

theorem alignmentCost_range_bddBelow (W V : LatinonMeasure) :
    BddBelow (Set.range (fun p : LatinonRelabel × LatinonRelabel => latinonAlignmentCost W V p.1 p.2)) :=
  ⟨0,by rintro _ ⟨p,rfl⟩; exact latinonAlignmentCost_nonneg W V p.1 p.2⟩

theorem latinonCutDistance_nonneg (W V : LatinonMeasure) : 0 ≤ latinonCutDistance W V :=
  le_csInf (alignmentCost_range_nonempty W V)
    (by rintro _ ⟨p,rfl⟩; exact latinonAlignmentCost_nonneg W V p.1 p.2)

theorem latinonCutDistance_le_cost (W V : LatinonMeasure) (e f : LatinonRelabel) :
    latinonCutDistance W V ≤ latinonAlignmentCost W V e f :=
  csInf_le (alignmentCost_range_bddBelow W V) ⟨(e,f),rfl⟩

theorem latinonCutDistance_le_three (W V : LatinonMeasure) : latinonCutDistance W V ≤ 3 :=
  (latinonCutDistance_le_cost W V LatinonRelabel.refl LatinonRelabel.refl).trans
    (latinonAlignmentCost_le_three W V LatinonRelabel.refl LatinonRelabel.refl)

theorem latinonCutDistance_self (W : LatinonMeasure) : latinonCutDistance W W = 0 := by
  have hc : latinonAlignmentCost W W LatinonRelabel.refl LatinonRelabel.refl = 0 := by
    change orderCut W.order W.order+orderCut W.order W.order+
      measureCut W.measure (relabelLatinonMeasure W.measure LatinonRelabel.refl LatinonRelabel.refl) = 0
    rw [orderCut_self,relabelLatinonMeasure_refl,measureCut_self]
    norm_num
  exact le_antisymm
    ((latinonCutDistance_le_cost W W LatinonRelabel.refl LatinonRelabel.refl).trans_eq hc)
    (latinonCutDistance_nonneg W W)

theorem exists_alignmentCost_lt (W V : LatinonMeasure) (delta : ℝ)
    (h : latinonCutDistance W V < delta) :
    ∃ e f : LatinonRelabel, latinonAlignmentCost W V e f < delta := by
  by_contra hn
  have hl : delta ≤ latinonCutDistance W V := by
    apply le_csInf (alignmentCost_range_nonempty W V)
    rintro _ ⟨p,rfl⟩
    exact le_of_not_gt (fun hc => hn ⟨p.1,p.2,hc⟩)
  exact (not_lt_of_ge hl) h

theorem exists_alignment_of_cutDistance_lt (W V : LatinonMeasure) (delta : ℝ)
    (h : latinonCutDistance W V < delta) :
    ∃ e f : LatinonRelabel,
      orderCut W.order (V.order ∘ e) < delta ∧
      orderCut W.order (V.order ∘ f) < delta ∧
      measureCut W.measure (relabelLatinonMeasure V.measure e f) < delta := by
  obtain ⟨e,f,hc⟩ := exists_alignmentCost_lt W V delta h
  exact ⟨e,f,(row_orderCut_le_alignmentCost W V e f).trans_lt hc,
    (col_orderCut_le_alignmentCost W V e f).trans_lt hc,
    (measureCut_le_alignmentCost W V e f).trans_lt hc⟩

theorem exists_box_alignment_of_cutDistance_lt (W V : LatinonMeasure) (delta : ℝ)
    (h : latinonCutDistance W V < delta) :
    ∃ e f : LatinonRelabel, ∀ B : LatinonBox,
      |W.measure.real B.carrier-(relabelLatinonMeasure V.measure e f).real B.carrier| < delta := by
  obtain ⟨e,f,_,_,hc⟩ := exists_alignment_of_cutDistance_lt W V delta h
  exact ⟨e,f,fun B => (measureCut_test_le _ _ B).trans_lt hc⟩

end LatinonEntropy

#print axioms LatinonEntropy.latinonAlignmentCost_nonneg
#print axioms LatinonEntropy.latinonAlignmentCost_le_three
#print axioms LatinonEntropy.latinonCutDistance_nonneg
#print axioms LatinonEntropy.latinonCutDistance_le_cost
#print axioms LatinonEntropy.latinonCutDistance_le_three
#print axioms LatinonEntropy.latinonCutDistance_self
#print axioms LatinonEntropy.exists_alignmentCost_lt
#print axioms LatinonEntropy.exists_alignment_of_cutDistance_lt
#print axioms LatinonEntropy.exists_box_alignment_of_cutDistance_lt
