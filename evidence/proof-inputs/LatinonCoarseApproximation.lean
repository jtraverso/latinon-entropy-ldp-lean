module

public import LatinonCompressionPatterns
public import LatinonSymbolCollisions

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem coarsePatternDensity_le {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternDensity W P q ≤ latinonPatternDensity W P := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact measureReal_mono (Set.prod_mono Set.Subset.rfl (coarsePatternRealizations_subset P hq))

theorem latinonPatternDensity_coarse_error {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    |latinonPatternDensity W P-coarsePatternDensity W P q| ≤
      ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  let A := orderedLatinonPatternConfigs W k l ×ˢ unitOrderPatternRealizations P
  let B := orderedLatinonPatternConfigs W k l ×ˢ coarsePatternRealizations P q
  let C : Set (LatinonPatternConfig k l × ((Fin k × Fin l) → I)) :=
    Set.univ ×ˢ symbolGridCollision k l q
  have hmono : (latinonPatternSampleLaw W k l) (A \ B) ≤
      (latinonPatternSampleLaw W k l) C := by
    apply measure_mono_ae
    filter_upwards [latinonPatternSampleLaw_grid_cover W k l hq] with p hp
    intro hab
    refine ⟨Set.mem_univ _,?_⟩
    by_contra hn
    apply hab.2
    exact ⟨hab.1.1,mem_coarsePatternRealizations_of_no_collision P hq p.2 hab.1.2 hp hn⟩
  have hr : (latinonPatternSampleLaw W k l).real (A \ B) ≤
      (latinonPatternSampleLaw W k l).real C :=
    ENNReal.toReal_mono (measure_ne_top _ _) hmono
  have hnonneg : 0 ≤ latinonPatternDensity W P-coarsePatternDensity W P q :=
    sub_nonneg.mpr (coarsePatternDensity_le W P hq)
  rw [abs_of_nonneg hnonneg]
  change ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real A-
    ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real B ≤ _
  rw [← mul_sub]
  calc
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real (A \ B) :=
      mul_le_mul_of_nonneg_left le_measureReal_sdiff (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(latinonPatternSampleLaw W k l).real C :=
      mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
    _ ≤ ((k.factorial*l.factorial : ℕ) : ℝ)*(((k*l : ℕ) : ℝ)^2/(q : ℝ)) :=
      mul_le_mul_of_nonneg_left (latinonPatternSampleLaw_collision_le W k l hq) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem latinonPatternDensity_polynomial_error {k l q : ℕ} (W : LatinonMeasure)
    (P : LatinOrderPattern k l) (hq : 0 < q) :
    |latinonPatternDensity W P-compressionPatternPolynomial W P q| ≤
      ((k.factorial*l.factorial : ℕ) : ℝ)*((k*l : ℕ) : ℝ)^2/(q : ℝ) := by
  rw [← coarsePatternDensity_eq_polynomial W P hq]
  exact latinonPatternDensity_coarse_error W P hq

end LatinonEntropy

#print axioms LatinonEntropy.coarsePatternDensity_le
#print axioms LatinonEntropy.latinonPatternDensity_coarse_error
#print axioms LatinonEntropy.latinonPatternDensity_polynomial_error
