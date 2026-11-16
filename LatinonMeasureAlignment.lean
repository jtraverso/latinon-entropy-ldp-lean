module

public import LatinonRelabel

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def inverseCoordinateRelabel (e f : LatinonRelabel) (p : LatinonPoint) : LatinonPoint :=
  ((e.symm p.1.1,f.symm p.1.2),p.2)

theorem inverseCoordinateRelabel_measurable (e f : LatinonRelabel) :
    Measurable (inverseCoordinateRelabel e f) :=
  ((e.symm.measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    (f.symm.measurable.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd

/-- Pullback of the row and column coordinates: the pushforward uses inverses. -/
def relabelLatinonMeasure (mu : Measure LatinonPoint) (e f : LatinonRelabel) : Measure LatinonPoint :=
  mu.map (inverseCoordinateRelabel e f)

instance (mu : Measure LatinonPoint) [IsProbabilityMeasure mu] (e f : LatinonRelabel) :
    IsProbabilityMeasure (relabelLatinonMeasure mu e f) where
  measure_univ := by
    unfold relabelLatinonMeasure
    rw [Measure.map_apply (inverseCoordinateRelabel_measurable e f) MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]

theorem relabelLatinonMeasure_box (mu : Measure LatinonPoint) (e f : LatinonRelabel)
    (S T U : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    relabelLatinonMeasure mu e f ((S ×ˢ T) ×ˢ U) =
      mu (((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T)) ×ˢ U) := by
  unfold relabelLatinonMeasure
  rw [Measure.map_apply (inverseCoordinateRelabel_measurable e f) ((hS.prod hT).prod hU)]
  rfl

theorem relabelLatinonMeasure_real_box (mu : Measure LatinonPoint) (e f : LatinonRelabel)
    (S T U : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    (relabelLatinonMeasure mu e f).real ((S ×ˢ T) ×ˢ U) =
      mu.real (((e.symm ⁻¹' S) ×ˢ (f.symm ⁻¹' T)) ×ˢ U) := by
  simpa only [measureReal_def] using
    congrArg ENNReal.toReal (relabelLatinonMeasure_box mu e f S T U hS hT hU)

theorem relabelLatinonMeasure_xy (W : LatinonMeasure) (e f : LatinonRelabel)
    (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    relabelLatinonMeasure W.measure e f ((S ×ˢ T) ×ˢ Set.univ) = volume S*volume T := by
  rw [relabelLatinonMeasure_box _ e f S T Set.univ hS hT MeasurableSet.univ,
    W.xy_uniform _ _ (hS.preimage e.symm.measurable) (hT.preimage f.symm.measurable),
    e.symm.preserves.measure_preimage hS.nullMeasurableSet,
    f.symm.preserves.measure_preimage hT.nullMeasurableSet]

theorem relabelLatinonMeasure_xz (W : LatinonMeasure) (e f : LatinonRelabel)
    (S U : Set I) (hS : MeasurableSet S) (hU : MeasurableSet U) :
    relabelLatinonMeasure W.measure e f ((S ×ˢ Set.univ) ×ˢ U) = volume S*volume U := by
  rw [relabelLatinonMeasure_box _ e f S Set.univ U hS MeasurableSet.univ hU]
  simp only [Set.preimage_univ]
  rw [W.xz_uniform _ _ (hS.preimage e.symm.measurable) hU,
    e.symm.preserves.measure_preimage hS.nullMeasurableSet]

theorem relabelLatinonMeasure_yz (W : LatinonMeasure) (e f : LatinonRelabel)
    (T U : Set I) (hT : MeasurableSet T) (hU : MeasurableSet U) :
    relabelLatinonMeasure W.measure e f ((Set.univ ×ˢ T) ×ˢ U) = volume T*volume U := by
  rw [relabelLatinonMeasure_box _ e f Set.univ T U MeasurableSet.univ hT hU]
  simp only [Set.preimage_univ]
  rw [W.yz_uniform _ _ (hT.preimage f.symm.measurable) hU,
    f.symm.preserves.measure_preimage hT.nullMeasurableSet]

theorem relabelLatinonMeasure_refl (mu : Measure LatinonPoint) :
    relabelLatinonMeasure mu LatinonRelabel.refl LatinonRelabel.refl = mu := by
  unfold relabelLatinonMeasure
  have he : inverseCoordinateRelabel LatinonRelabel.refl LatinonRelabel.refl = id := by
    funext p
    rcases p with ⟨⟨x,y⟩,z⟩
    rfl
  rw [he,Measure.map_id]

end LatinonEntropy

#print axioms LatinonEntropy.inverseCoordinateRelabel_measurable
#print axioms LatinonEntropy.relabelLatinonMeasure_box
#print axioms LatinonEntropy.relabelLatinonMeasure_real_box
#print axioms LatinonEntropy.relabelLatinonMeasure_xy
#print axioms LatinonEntropy.relabelLatinonMeasure_xz
#print axioms LatinonEntropy.relabelLatinonMeasure_yz
#print axioms LatinonEntropy.relabelLatinonMeasure_refl
