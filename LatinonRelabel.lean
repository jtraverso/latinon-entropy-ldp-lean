module

public import LatinonMeasureSpace

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- The actual measurable measure-preserving bijections used in the cut distance. -/
structure LatinonRelabel where
  equiv : I ≃ᵐ I
  preserves : MeasurePreserving equiv volume volume

instance : CoeFun LatinonRelabel (fun _ => I → I) := ⟨fun e => e.equiv⟩

namespace LatinonRelabel

def refl : LatinonRelabel := ⟨MeasurableEquiv.refl I,MeasurePreserving.id volume⟩

def symm (e : LatinonRelabel) : LatinonRelabel :=
  ⟨e.equiv.symm,MeasurePreserving.symm e.equiv e.preserves⟩

def trans (e f : LatinonRelabel) : LatinonRelabel :=
  ⟨e.equiv.trans f.equiv,f.preserves.comp e.preserves⟩

@[simp] theorem symm_apply_apply (e : LatinonRelabel) (x : I) : e.symm (e x) = x :=
  e.equiv.symm_apply_apply x

@[simp] theorem apply_symm_apply (e : LatinonRelabel) (x : I) : e (e.symm x) = x :=
  e.equiv.apply_symm_apply x

theorem measurable (e : LatinonRelabel) : Measurable e := e.equiv.measurable

theorem image_eq_inverse_preimage (e : LatinonRelabel) (S : Set I) :
    e '' S = e.symm ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [Set.mem_preimage,symm_apply_apply] using hy
  · intro hx
    exact ⟨e.symm x,hx,e.apply_symm_apply x⟩

theorem image_measurable (e : LatinonRelabel) (S : Set I) (hS : MeasurableSet S) :
    MeasurableSet (e '' S) := by
  rw [e.image_eq_inverse_preimage]
  exact hS.preimage e.symm.measurable

theorem image_measure (e : LatinonRelabel) (S : Set I) (hS : MeasurableSet S) :
    volume (e '' S) = volume S := by
  rw [e.image_eq_inverse_preimage]
  exact e.symm.preserves.measure_preimage hS.nullMeasurableSet

theorem inverse_image_inter_mass (e : LatinonRelabel) (S T : Set I)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    volume.real (e.symm ⁻¹' S ∩ T) = volume.real (S ∩ e ⁻¹' T) := by
  have he : e ⁻¹' (e.symm ⁻¹' S ∩ T) = S ∩ e ⁻¹' T := by
    ext x
    simp only [Set.mem_preimage,Set.mem_inter_iff,e.symm_apply_apply]
  have hm := e.preserves.measureReal_preimage
    ((hS.preimage e.symm.measurable).inter hT).nullMeasurableSet
  rw [he] at hm
  exact hm.symm

end LatinonRelabel

example : Nonempty LatinonRelabel := ⟨LatinonRelabel.refl⟩

end LatinonEntropy

#print axioms LatinonEntropy.LatinonRelabel.symm
#print axioms LatinonEntropy.LatinonRelabel.trans
#print axioms LatinonEntropy.LatinonRelabel.image_eq_inverse_preimage
#print axioms LatinonEntropy.LatinonRelabel.image_measurable
#print axioms LatinonEntropy.LatinonRelabel.image_measure
#print axioms LatinonEntropy.LatinonRelabel.inverse_image_inter_mass
