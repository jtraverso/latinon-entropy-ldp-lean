module

public import LatinonFiniteIndexCollisions

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev PatternSampleSpace (k l : ℕ) := LatinonPatternConfig k l × ((Fin k × Fin l) → I)

def finitePatternConfigEvent {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (LatinonPatternConfig k l) := (patternConfigGridIndices n hn) ⁻¹' finiteMatrixPatternConfigs L P

def finitePatternSampleEvent {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (PatternSampleSpace k l) := Prod.fst ⁻¹' finitePatternConfigEvent hn L P

def finitePatternBadEvent (n : ℕ) (hn : 0 < n) (k l : ℕ) : Set (PatternSampleSpace k l) :=
  (gridIndexFamilyCollision (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i) n hn ∪
    gridIndexFamilyCollision (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j) n hn) ∪
      gridIndexFamilyCollision (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a) n hn

def patternBridgeConstant (k l : ℕ) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)

theorem finiteMatrixPatternDensity_eq_sample_probability {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finiteMatrixPatternDensity L P=((k.factorial*l.factorial : ℕ) : ℝ)*
      (latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l).real (finitePatternSampleEvent hn L P) := by
  rw [finiteMatrixPatternDensity_eq_config_probability hn L P]
  congr 1
  have hE : MeasurableSet (finitePatternConfigEvent hn L P) :=
    (Set.toFinite (finiteMatrixPatternConfigs L P)).measurableSet.preimage
      (patternConfigGridIndices_preserving n hn k l).measurable
  exact ((latinonPatternSampleLaw_config_preserving (latinArrayToLatinonMeasure hn L) k l).measureReal_preimage
    hE.nullMeasurableSet).symm

theorem finitePatternSampleEvent_subset_pattern_ae {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finitePatternSampleEvent hn L P ≤ᵐ[latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l]
      latinonPatternEvent (latinArrayToLatinonMeasure hn L) P := by
  filter_upwards [finite_sample_symbol_indices hn L] with p hp
  intro he
  change StrictMono (fun i => unitGridIndex n hn (p.1.1 i)) ∧
    StrictMono (fun j => unitGridIndex n hn (p.1.2 j)) ∧
      (∀ a b, P a < P b →
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) <
          L.val (unitGridIndex n hn (p.1.1 b.1)) (unitGridIndex n hn (p.1.2 b.2))) at he
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i j hij
    exact unitGridIndex_strict_reflect n hn (he.1 hij)
  · intro i j hij
    exact unitGridIndex_strict_reflect n hn (he.2.1 hij)
  · intro a b hab
    apply unitGridIndex_strict_reflect n hn
    rw [hp a,hp b]
    exact he.2.2 a b hab

theorem finitePatternSampleEvent_difference_subset_ae {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    latinonPatternEvent (latinArrayToLatinonMeasure hn L) P \ finitePatternSampleEvent hn L P
      ≤ᵐ[latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l] finitePatternBadEvent n hn k l := by
  filter_upwards [finite_sample_symbol_indices hn L] with p hp
  intro hdiff
  by_contra hnot
  have hr : Function.Injective (fun i : Fin k => unitGridIndex n hn (p.1.1 i)) := by
    by_contra h
    exact hnot (Or.inl (Or.inl h))
  have hc : Function.Injective (fun j : Fin l => unitGridIndex n hn (p.1.2 j)) := by
    by_contra h
    exact hnot (Or.inl (Or.inr h))
  have hz : Function.Injective (fun a : Fin k × Fin l => unitGridIndex n hn (p.2 a)) := by
    by_contra h
    exact hnot (Or.inr h)
  apply hdiff.2
  change StrictMono (fun i => unitGridIndex n hn (p.1.1 i)) ∧
    StrictMono (fun j => unitGridIndex n hn (p.1.2 j)) ∧
      (∀ a b, P a < P b →
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) <
          L.val (unitGridIndex n hn (p.1.1 b.1)) (unitGridIndex n hn (p.1.2 b.2)))
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    apply lt_of_le_of_ne
    · exact unitGridIndex_monotone n hn (hdiff.1.1.1 hij).le
    · exact fun he => (ne_of_lt hij) (hr he)
  · intro i j hij
    apply lt_of_le_of_ne
    · exact unitGridIndex_monotone n hn (hdiff.1.1.2 hij).le
    · exact fun he => (ne_of_lt hij) (hc he)
  · intro a b hab
    have hv : p.2 a < p.2 b := hdiff.1.2 a b hab
    have hne : a ≠ b := fun he => (ne_of_lt hab) (congrArg P he)
    have hi : unitGridIndex n hn (p.2 a) < unitGridIndex n hn (p.2 b) :=
      lt_of_le_of_ne (unitGridIndex_monotone n hn hv.le) (fun he => hne (hz he))
    simpa only [hp a,hp b] using hi

theorem finitePatternBadEvent_measure_le {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) :
    (latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l).real (finitePatternBadEvent n hn k l) ≤
      ((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)/(n : ℝ) := by
  let W := latinArrayToLatinonMeasure hn L
  let μ := latinonPatternSampleLaw W k l
  let R := gridIndexFamilyCollision (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i) n hn
  let C := gridIndexFamilyCollision (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j) n hn
  let Z := gridIndexFamilyCollision (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a) n hn
  have hr : μ.real R ≤ (k : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (i : Fin k) (p : PatternSampleSpace k l) => p.1.1 i)
      (fun i j hij => latinonPatternSampleLaw_row_pair_preserving W i j hij) n hn
  have hc : μ.real C ≤ (l : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (j : Fin l) (p : PatternSampleSpace k l) => p.1.2 j)
      (fun i j hij => latinonPatternSampleLaw_col_pair_preserving W i j hij) n hn
  have hz : μ.real Z ≤ ((k*l : ℕ) : ℝ)^2/(n : ℝ) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using gridIndex_family_collision_le μ
      (fun (a : Fin k × Fin l) (p : PatternSampleSpace k l) => p.2 a)
      (fun a b hab => latinonPatternSampleLaw_pair_preserving W a b hab) n hn
  change μ.real ((R ∪ C) ∪ Z) ≤ _
  have hrc : μ.real (R ∪ C) ≤ μ.real R+μ.real C := measureReal_union_le R C
  calc
    _ ≤ μ.real (R ∪ C)+μ.real Z := measureReal_union_le _ _
    _ ≤ (μ.real R+μ.real C)+μ.real Z := add_le_add hrc (le_refl _)
    _ ≤ ((k : ℝ)^2/(n : ℝ)+(l : ℝ)^2/(n : ℝ))+((k*l : ℕ) : ℝ)^2/(n : ℝ) :=
      add_le_add (add_le_add hr hc) hz
    _ = _ := by ring

/-- Uniform transfer from the actual embedded Latinon to the explicit
finite matrix count.No surrogate statistic or density hypothesis. -/
theorem finite_matrix_pattern_embedding_error {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    |latinonPatternDensity (latinArrayToLatinonMeasure hn L) P-finiteMatrixPatternDensity L P| ≤
      patternBridgeConstant k l/(n : ℝ) := by
  let μ := latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l
  let A := latinonPatternEvent (latinArrayToLatinonMeasure hn L) P
  let E := finitePatternSampleEvent hn L P
  have hmono : μ.real E ≤ μ.real A :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (finitePatternSampleEvent_subset_pattern_ae hn L P))
  have hbad : μ.real (A \ E) ≤ μ.real (finitePatternBadEvent n hn k l) :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (finitePatternSampleEvent_difference_subset_ae hn L P))
  rw [finiteMatrixPatternDensity_eq_sample_probability hn L P]
  change |((k.factorial*l.factorial : ℕ) : ℝ)*μ.real A-
    ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real E| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (sub_nonneg.mpr hmono)]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (A \ E) :=
      mul_le_mul_of_nonneg_left le_measureReal_sdiff (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*μ.real (finitePatternBadEvent n hn k l) :=
      mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(((k : ℝ)^2+(l : ℝ)^2+((k*l : ℕ) : ℝ)^2)/(n : ℝ)) :=
      mul_le_mul_of_nonneg_left (finitePatternBadEvent_measure_le hn L) (Nat.cast_nonneg _)
    _ = _ := by unfold patternBridgeConstant; ring

end LatinonEntropy

#print axioms LatinonEntropy.finiteMatrixPatternDensity_eq_sample_probability
#print axioms LatinonEntropy.finitePatternSampleEvent_subset_pattern_ae
#print axioms LatinonEntropy.finitePatternSampleEvent_difference_subset_ae
#print axioms LatinonEntropy.finitePatternBadEvent_measure_le
#print axioms LatinonEntropy.finite_matrix_pattern_embedding_error
