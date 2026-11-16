module

public import GridIntervalPermutation
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem real_volume_translate_image (a : ℝ) (T : Set ℝ) :
    volume ((fun x => x+a) '' T) = volume T := by
  have he : (fun x => x+a) '' T = (fun x => x+(-a)) ⁻¹' T := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,add_assoc,add_neg_cancel,add_zero] using hy
    · intro hx
      exact ⟨x+(-a),hx,by simp only [add_assoc,neg_add_cancel,add_zero]⟩
  rw [he,measure_preimage_add_right]

theorem gridIntervalPermutation_cell_image {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    (i : Fin n) (S : Set I) :
    gridIntervalPermutation hn sigma '' (lebesgueGridCell i ∩ gridIntervalPermutation hn sigma ⁻¹' S) =
      lebesgueGridCell (sigma i) ∩ S := by
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨gridIntervalPermutation_cell hn sigma hu.1,hu.2⟩
  · intro hv
    have hmem : gridIntervalPermutation hn sigma.symm v ∈ lebesgueGridCell i := by
      simpa only [sigma.symm_apply_apply] using gridIntervalPermutation_cell hn sigma.symm hv.1
    have hinv : gridIntervalPermutation hn sigma (gridIntervalPermutation hn sigma.symm v) = v := by
      simpa only [Equiv.symm_symm] using gridIntervalPermutation_inverse hn sigma.symm v
    refine ⟨gridIntervalPermutation hn sigma.symm v,⟨hmem,?_⟩,?_⟩
    · change gridIntervalPermutation hn sigma (gridIntervalPermutation hn sigma.symm v) ∈ S
      rw [hinv]
      exact hv.2
    · exact hinv

theorem gridIntervalPermutation_cell_mass {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    (i : Fin n) (S : Set I) :
    volume (lebesgueGridCell i ∩ gridIntervalPermutation hn sigma ⁻¹' S) =
      volume (lebesgueGridCell (sigma i) ∩ S) := by
  let T := lebesgueGridCell i ∩ gridIntervalPermutation hn sigma ⁻¹' S
  have he : ((↑) : I → ℝ) '' (gridIntervalPermutation hn sigma '' T) =
      (fun x : ℝ => x+gridIntervalShift sigma i) '' (((↑) : I → ℝ) '' T) := by
    rw [Set.image_image,Set.image_image]
    apply Set.image_congr
    intro u hu
    exact gridIntervalPermutation_val_of_mem hn sigma hu.1
  symm
  calc
    volume (lebesgueGridCell (sigma i) ∩ S)
        = volume (gridIntervalPermutation hn sigma '' T) := by
          rw [gridIntervalPermutation_cell_image hn sigma i S]
    _ = (volume : Measure ℝ) (((↑) : I → ℝ) '' (gridIntervalPermutation hn sigma '' T)) :=
      unitInterval.volume_apply
    _ = (volume : Measure ℝ) ((fun x : ℝ => x+gridIntervalShift sigma i) '' (((↑) : I → ℝ) '' T)) := by rw [he]
    _ = (volume : Measure ℝ) (((↑) : I → ℝ) '' T) := real_volume_translate_image _ _
    _ = volume T := unitInterval.volume_apply.symm

/-- Exact preservation,including the exceptional endpoint fixed at zero. -/
theorem gridIntervalPermutation_preserves {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n)) :
    MeasurePreserving (gridIntervalPermutation hn sigma) volume volume := by
  have hg := gridIntervalPermutation_measurable hn sigma
  refine ⟨hg,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hg hS]
  apply (measureReal_eq_measureReal_iff).mp
  let G := lebesgueGridPartition n hn
  rw [← G.sum_real_inter _ (hS.preimage hg)]
  calc
    (∑ i, (volume : Measure I).real (G.cell i ∩ gridIntervalPermutation hn sigma ⁻¹' S))
        = ∑ i, (volume : Measure I).real (lebesgueGridCell (sigma i) ∩ S) := by
          apply sum_congr rfl
          intro i _
          exact congrArg ENNReal.toReal (gridIntervalPermutation_cell_mass hn sigma i S)
    _ = ∑ j, (volume : Measure I).real (lebesgueGridCell j ∩ S) :=
      Equiv.sum_comp sigma (fun j => (volume : Measure I).real (lebesgueGridCell j ∩ S))
    _ = (volume : Measure I).real S := G.sum_real_inter S hS

end LatinonEntropy

#print axioms LatinonEntropy.real_volume_translate_image
#print axioms LatinonEntropy.gridIntervalPermutation_cell_image
#print axioms LatinonEntropy.gridIntervalPermutation_cell_mass
#print axioms LatinonEntropy.gridIntervalPermutation_preserves
