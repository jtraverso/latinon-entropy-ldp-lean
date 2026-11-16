module

public import LatinonCutNorms
public import LatinonMeasureAlignment

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def transportedBox (e f : LatinonRelabel) (B : LatinonBox) : LatinonBox where
  rows := e.symm ⁻¹' B.rows
  cols := f.symm ⁻¹' B.cols
  rows_measurable := B.rows_measurable.preimage e.symm.measurable
  cols_measurable := B.cols_measurable.preimage f.symm.measurable
  symbols := B.symbols
  symbols_measurable := B.symbols_measurable
  symbols_interval := B.symbols_interval

theorem relabel_box_mass (mu : Measure LatinonPoint) (e f : LatinonRelabel) (B : LatinonBox) :
    (relabelLatinonMeasure mu e f).real B.carrier = mu.real (transportedBox e f B).carrier :=
  relabelLatinonMeasure_real_box mu e f B.rows B.cols B.symbols
    B.rows_measurable B.cols_measurable B.symbols_measurable

theorem relabelLatinonMeasure_comp (mu : Measure LatinonPoint) (e f g h : LatinonRelabel) :
    relabelLatinonMeasure (relabelLatinonMeasure mu g h) e f =
      relabelLatinonMeasure mu (e.trans g) (f.trans h) := by
  unfold relabelLatinonMeasure
  rw [Measure.map_map (inverseCoordinateRelabel_measurable e f) (inverseCoordinateRelabel_measurable g h)]
  apply congrArg (fun k => mu.map k)
  funext p
  rcases p with ⟨⟨x,y⟩,z⟩
  rfl

theorem relabelLatinonMeasure_inverse (mu : Measure LatinonPoint) (e f : LatinonRelabel) :
    relabelLatinonMeasure (relabelLatinonMeasure mu e f) e.symm f.symm = mu := by
  unfold relabelLatinonMeasure
  rw [Measure.map_map (inverseCoordinateRelabel_measurable e.symm f.symm)
    (inverseCoordinateRelabel_measurable e f)]
  have he : inverseCoordinateRelabel e.symm f.symm ∘ inverseCoordinateRelabel e f = id := by
    funext p
    rcases p with ⟨⟨x,y⟩,z⟩
    change ((e (e.symm x),f (f.symm y)),z) = ((x,y),z)
    rw [e.apply_symm_apply,f.apply_symm_apply]
  rw [he,Measure.map_id]

theorem measureCut_relabel_le (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (e f : LatinonRelabel) :
    measureCut (relabelLatinonMeasure mu e f) (relabelLatinonMeasure nu e f) ≤ measureCut mu nu := by
  apply cutValueSup_le
  intro B
  rw [relabel_box_mass,relabel_box_mass]
  exact measureCut_test_le mu nu (transportedBox e f B)

theorem measureCut_relabel_invariant (mu nu : Measure LatinonPoint)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (e f : LatinonRelabel) :
    measureCut (relabelLatinonMeasure mu e f) (relabelLatinonMeasure nu e f) = measureCut mu nu := by
  have hr := measureCut_relabel_le (relabelLatinonMeasure mu e f) (relabelLatinonMeasure nu e f) e.symm f.symm
  rw [relabelLatinonMeasure_inverse,relabelLatinonMeasure_inverse] at hr
  exact le_antisymm (measureCut_relabel_le mu nu e f) hr

def transportedRectangle (e : LatinonRelabel) (R : LatinonRectangle) : LatinonRectangle where
  rows := e.symm ⁻¹' R.rows
  cols := e.symm ⁻¹' R.cols
  rows_measurable := R.rows_measurable.preimage e.symm.measurable
  cols_measurable := R.cols_measurable.preimage e.symm.measurable

theorem orderBox_comp (f : I → I) (hf : Measurable f) (e : LatinonRelabel) (R : LatinonRectangle) :
    orderBox (f ∘ e) R = orderBox f (transportedRectangle e R) := by
  have hset : MeasurableSet
      (((e.symm ⁻¹' R.rows) ×ˢ (e.symm ⁻¹' R.cols)) ∩ orderRelation f) :=
    ((R.rows_measurable.preimage e.symm.measurable).prod
      (R.cols_measurable.preimage e.symm.measurable)).inter (orderRelation_measurable f hf)
  have he : Prod.map e e ⁻¹'
      (((e.symm ⁻¹' R.rows) ×ˢ (e.symm ⁻¹' R.cols)) ∩ orderRelation f) =
      (R.rows ×ˢ R.cols) ∩ orderRelation (f ∘ e) := by
    ext p
    rcases p with ⟨u,v⟩
    change ((e.symm (e u) ∈ R.rows ∧ e.symm (e v) ∈ R.cols) ∧ f (e u) < f (e v)) ↔
      ((u ∈ R.rows ∧ v ∈ R.cols) ∧ (f ∘ e) u < (f ∘ e) v)
    rw [e.symm_apply_apply,e.symm_apply_apply]
    rfl
  have hm := (e.preserves.prod e.preserves).measureReal_preimage hset.nullMeasurableSet
  rw [he] at hm
  exact hm

theorem orderCut_comp_le (f g : I → I) (hf : Measurable f) (hg : Measurable g) (e : LatinonRelabel) :
    orderCut (f ∘ e) (g ∘ e) ≤ orderCut f g := by
  apply cutValueSup_le
  intro R
  rw [orderBox_comp f hf e R,orderBox_comp g hg e R]
  exact orderCut_test_le f g (transportedRectangle e R)

theorem relabel_comp_inverse_cancel (f : I → I) (e : LatinonRelabel) : (f ∘ e) ∘ e.symm = f := by
  funext x
  change f (e (e.symm x)) = f x
  rw [e.apply_symm_apply]

theorem orderCut_comp_invariant (f g : I → I) (hf : Measurable f) (hg : Measurable g)
    (e : LatinonRelabel) : orderCut (f ∘ e) (g ∘ e) = orderCut f g := by
  have hr := orderCut_comp_le (f ∘ e) (g ∘ e) (hf.comp e.measurable) (hg.comp e.measurable) e.symm
  rw [relabel_comp_inverse_cancel,relabel_comp_inverse_cancel] at hr
  exact le_antisymm (orderCut_comp_le f g hf hg e) hr

end LatinonEntropy

#print axioms LatinonEntropy.relabelLatinonMeasure_comp
#print axioms LatinonEntropy.relabelLatinonMeasure_inverse
#print axioms LatinonEntropy.measureCut_relabel_invariant
#print axioms LatinonEntropy.orderBox_comp
#print axioms LatinonEntropy.orderCut_comp_invariant
