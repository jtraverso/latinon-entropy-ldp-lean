module

public import LatinonOrderPermutation
public import LatinGridBallLowerBound

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem sum_reindex_profile_rows_cols {n : ℕ} (t : Fin n → Fin n → Fin n → ℝ)
    (sigma : Equiv.Perm (Fin n)) :
    (∑ x, ∑ y, ∑ z, t (sigma.symm x) (sigma.symm y) z) = ∑ x, ∑ y, ∑ z, t x y z := by
  have hy : ∀ x : Fin n, (∑ y, ∑ z, t (sigma.symm x) (sigma.symm y) z) =
      ∑ y, ∑ z, t (sigma.symm x) y z := fun x =>
    Equiv.sum_comp sigma.symm (fun y => ∑ z, t (sigma.symm x) y z)
  simp_rw [hy]
  exact Equiv.sum_comp sigma.symm (fun x => ∑ y, ∑ z, t x y z)

def permutePositiveLatinProfile {n : ℕ} (P : PositiveLatinProfile n)
    (sigma : Equiv.Perm (Fin n)) : PositiveLatinProfile n where
  npos := P.npos
  p := fun x y z => P.p (sigma.symm x) (sigma.symm y) z
  a := P.a
  b := P.b
  a_pos := P.a_pos
  a_le_b := P.a_le_b
  bounds := fun x y z => P.bounds (sigma.symm x) (sigma.symm y) z
  row_mass := fun x y => P.row_mass (sigma.symm x) (sigma.symm y)
  col_mass := fun x z => (Equiv.sum_comp sigma.symm (fun y => P.p (sigma.symm x) y z)).trans
    (P.col_mass (sigma.symm x) z)
  time_mass := fun y z => (Equiv.sum_comp sigma.symm (fun x => P.p x (sigma.symm y) z)).trans
    (P.time_mass (sigma.symm y) z)

theorem permute_profile_density_entropy {n : ℕ} (P : PositiveLatinProfile n)
    (sigma : Equiv.Perm (Fin n)) :
    latinGridDensityEntropy (fun x y z => (n : ℝ)*(permutePositiveLatinProfile P sigma).p x y z) =
      latinGridDensityEntropy (fun x y z => (n : ℝ)*P.p x y z) := by
  unfold latinGridDensityEntropy
  change -(∑ x, ∑ y, ∑ z, ((n : ℝ)*P.p (sigma.symm x) (sigma.symm y) z)*
      Real.log ((n : ℝ)*P.p (sigma.symm x) (sigma.symm y) z))/(n : ℝ)^3 = _
  rw [sum_reindex_profile_rows_cols
    (fun x y z => ((n : ℝ)*P.p x y z)*Real.log ((n : ℝ)*P.p x y z)) sigma]

theorem grid_relabel_inverse_cell_mass {n : ℕ} (hn : 0 < n) (sigma : Equiv.Perm (Fin n))
    (i : Fin n) (S : Set I) :
    (volume : Measure I).real ((gridIntervalRelabel hn sigma).symm ⁻¹' S ∩ lebesgueGridCell (sigma i)) =
      volume.real (S ∩ lebesgueGridCell i) := by
  have hh := congrArg ENNReal.toReal (gridIntervalPermutation_cell_mass hn sigma.symm (sigma i) S)
  simp only [Equiv.symm_apply_apply] at hh
  rw [Set.inter_comm (lebesgueGridCell (sigma i)),Set.inter_comm (lebesgueGridCell i)] at hh
  exact hh

/-- The profile permutation and the admissible interval relabeling cancel
EXACTLY as measures. This uses the inverse convention of the full distance. -/
theorem permuted_profile_relabel_measure {n : ℕ} (P : PositiveLatinProfile n)
    (sigma : Equiv.Perm (Fin n)) :
    relabelLatinonMeasure (profileToLatinonMeasure (permutePositiveLatinProfile P sigma)).measure
      (gridIntervalRelabel P.npos sigma) (gridIntervalRelabel P.npos sigma) =
        (profileToLatinonMeasure P).measure := by
  let e := gridIntervalRelabel P.npos sigma
  let Q := permutePositiveLatinProfile P sigma
  apply Measure.ext_prod₃'
  intro S T U hS hT hU
  apply (measureReal_eq_measureReal_iff).mp
  rw [relabelLatinonMeasure_real_box _ e e S T U hS hT hU]
  change (gridTensorMeasure Q.p).real (((e.symm ⁻¹' S) ×ˢ (e.symm ⁻¹' T)) ×ˢ U) =
    (gridTensorMeasure P.p).real ((S ×ˢ T) ×ˢ U)
  rw [gridTensorMeasure_real_box Q.p (fun x y z => (Q.entry_pos x y z).le),
    gridTensorMeasure_real_box P.p (fun x y z => (P.entry_pos x y z).le)]
  let F : Fin n → Fin n → Fin n → ℝ := fun x y z => Q.p x y z*
    volume.real ((e.symm ⁻¹' S) ∩ lebesgueGridCell x)*
      volume.real ((e.symm ⁻¹' T) ∩ lebesgueGridCell y)*volume.real (U ∩ lebesgueGridCell z)
  apply congrArg (fun r : ℝ => (n : ℝ)*r)
  calc
    (∑ x, ∑ y, ∑ z, F x y z) = ∑ i, ∑ y, ∑ z, F (sigma i) y z :=
      (Equiv.sum_comp sigma (fun x => ∑ y, ∑ z, F x y z)).symm
    _ = ∑ i, ∑ j, ∑ z, F (sigma i) (sigma j) z := by
      apply sum_congr rfl
      intro i _
      exact (Equiv.sum_comp sigma (fun y => ∑ z, F (sigma i) y z)).symm
    _ = ∑ i, ∑ j, ∑ z, P.p i j z*volume.real (S ∩ lebesgueGridCell i)*
        volume.real (T ∩ lebesgueGridCell j)*volume.real (U ∩ lebesgueGridCell z) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro z _
      dsimp only [F,Q,permutePositiveLatinProfile]
      rw [sigma.symm_apply_apply,sigma.symm_apply_apply,
        grid_relabel_inverse_cell_mass P.npos sigma i S,
        grid_relabel_inverse_cell_mass P.npos sigma j T]

end LatinonEntropy

#print axioms LatinonEntropy.sum_reindex_profile_rows_cols
#print axioms LatinonEntropy.permutePositiveLatinProfile
#print axioms LatinonEntropy.permute_profile_density_entropy
#print axioms LatinonEntropy.grid_relabel_inverse_cell_mass
#print axioms LatinonEntropy.permuted_profile_relabel_measure
