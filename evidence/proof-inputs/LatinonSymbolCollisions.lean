module

public import LatinonSymbolPairs
public import LatinonCoarsePatterns

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem latinonPatternSampleLaw_grid_cover (W : LatinonMeasure) (k l : ℕ)
    {q : ℕ} (hq : 0 < q) :
    ∀ᵐ p ∂latinonPatternSampleLaw W k l,
      ∀ a : Fin k × Fin l, ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j := by
  simp only [ae_all_iff]
  intro a
  exact (latinonPatternSampleLaw_single_preserving W a).quasiMeasurePreserving.ae
    (lebesgueGridCell_cover_ae hq)

theorem latinonPatternSampleLaw_pair_collision_le (W : LatinonMeasure) {k l q : ℕ}
    (hq : 0 < q) (a b : Fin k × Fin l) (hab : a ≠ b) :
    (latinonPatternSampleLaw W k l).real
      {p | ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j} ≤ 1/(q : ℝ) := by
  let E := fun j : Fin q =>
    (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.2 a,p.2 b)) ⁻¹'
      (lebesgueGridCell j ×ˢ lebesgueGridCell j)
  have he : {p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) |
      ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j}=⋃ j, E j := by
    ext p
    simp only [E,Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_prod]
  have hmass (j : Fin q) :
      (latinonPatternSampleLaw W k l).real (E j)=(1/(q : ℝ))^2 := by
    have h := congrArg ENNReal.toReal
      ((latinonPatternSampleLaw_pair_preserving W a b hab).measure_preimage
        ((lebesgueGridCell_measurable j).prod (lebesgueGridCell_measurable j)).nullMeasurableSet)
    change (latinonPatternSampleLaw W k l).real (E j)=
      unitSquareVolume.real (lebesgueGridCell j ×ˢ lebesgueGridCell j) at h
    rw [h,measureReal_prod_prod,lebesgueGridCell_mass hq j]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : Fin q, (latinonPatternSampleLaw W k l).real (E j) :=
      measureReal_iUnion_fintype_le E
    _ = (q : ℝ)*(1/(q : ℝ))^2 := by
      simp only [hmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = 1/(q : ℝ) := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hq : (0 : ℝ) < q)]

/-- A deliberately coarse, uniform O((kl)^2/q) bound. No density bound,
finite entropy, or pointwise control of conditional marginals is used. -/
theorem latinonPatternSampleLaw_collision_le (W : LatinonMeasure) (k l : ℕ)
    {q : ℕ} (hq : 0 < q) :
    (latinonPatternSampleLaw W k l).real (Set.univ ×ˢ symbolGridCollision k l q) ≤
      ((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  let E := fun a b : Fin k × Fin l =>
    if a=b then (∅ : Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)))
    else {p | ∃ j : Fin q, p.2 a ∈ lebesgueGridCell j ∧ p.2 b ∈ lebesgueGridCell j}
  have he : Set.univ ×ˢ symbolGridCollision k l q=⋃ a, ⋃ b, E a b := by
    ext p
    simp only [symbolGridCollision,Set.mem_prod,Set.mem_univ,true_and,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨a,b,hab,h⟩
      exact ⟨a,b,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h⟩
    · rintro ⟨a,b,h⟩
      by_cases hab : a=b
      · simp only [E,ite_eq_left hab,Set.mem_empty_iff_false] at h
      · exact ⟨a,b,hab,by simpa only [E,ite_eq_right hab,Set.mem_ofPred_eq] using h⟩
  have hcap (a b : Fin k × Fin l) :
      (latinonPatternSampleLaw W k l).real (E a b) ≤ 1/(q : ℝ) := by
    by_cases hab : a=b
    · simp only [E,ite_eq_left hab,measureReal_empty]
      exact div_nonneg zero_le_one (Nat.cast_nonneg q)
    · simpa only [E,ite_eq_right hab] using latinonPatternSampleLaw_pair_collision_le W hq a b hab
  rw [he]
  calc
    _ ≤ ∑ a : Fin k × Fin l, (latinonPatternSampleLaw W k l).real (⋃ b, E a b) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ a : Fin k × Fin l, ∑ b : Fin k × Fin l, (latinonPatternSampleLaw W k l).real (E a b) :=
      Finset.sum_le_sum (fun a _ => measureReal_iUnion_fintype_le (E a))
    _ ≤ ∑ _a : Fin k × Fin l, ∑ _b : Fin k × Fin l, 1/(q : ℝ) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcap a b))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.latinonPatternSampleLaw_grid_cover
#print axioms LatinonEntropy.latinonPatternSampleLaw_pair_collision_le
#print axioms LatinonEntropy.latinonPatternSampleLaw_collision_le
