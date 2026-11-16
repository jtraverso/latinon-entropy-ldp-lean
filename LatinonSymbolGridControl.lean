module

public import SymbolIntervalGridApproximation
public import LatinonWeakMarginalCompactness
public import LatinonCutNorms

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

theorem latinon_box_inner_symbol_error (W : LatinonMeasure) (S T U C : Set I)
    (hU : MeasurableSet U) (hC : MeasurableSet C) (hCU : C ⊆ U) :
    |W.measure.real ((S ×ˢ T) ×ˢ U)-W.measure.real ((S ×ˢ T) ×ˢ C)| ≤
      (volume : Measure I).real (U \ C) := by
  have hm : MeasurePreserving (Prod.snd : LatinonPoint → I) W.measure volume :=
    (measurePreserving_snd (μ := (volume : Measure I)) (ν := volume)).comp (latinon_xz_preserving W)
  have hproj : W.measure.real (Prod.snd ⁻¹' (U \ C))=(volume : Measure I).real (U \ C) :=
    congrArg ENNReal.toReal (hm.measure_preimage (hU.diff hC).nullMeasurableSet)
  have hsub : ((S ×ˢ T) ×ˢ C) ⊆ ((S ×ˢ T) ×ˢ U) := Set.prod_mono le_rfl hCU
  rw [abs_of_nonneg (sub_nonneg.mpr (measureReal_mono hsub))]
  calc
    _ ≤ W.measure.real (((S ×ˢ T) ×ˢ U) \ ((S ×ˢ T) ×ˢ C)) := le_measureReal_sdiff
    _ ≤ W.measure.real (Prod.snd ⁻¹' (U \ C)) := by
      apply measureReal_mono (μ := W.measure) ?_ (measure_ne_top W.measure _)
      intro p hp
      exact ⟨hp.1.2,fun hc => hp.2 ⟨hp.1.1,hc⟩⟩
    _ = _ := hproj

theorem latinon_box_grid_union_sum (W : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (F : Finset (Fin n)) (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    W.measure.real ((S ×ˢ T) ×ˢ symbolGridUnion F)=
      ∑ j ∈ F, W.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j) := by
  have he : ((S ×ˢ T) ×ˢ symbolGridUnion F)=⋃ j ∈ F, ((S ×ˢ T) ×ˢ lebesgueGridCell j) := by
    ext p
    simp only [symbolGridUnion,Set.mem_prod,Set.mem_iUnion]
    aesop
  rw [he]
  apply measureReal_biUnion_finset
  · intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hn i j hij) hp.2 hq.2
  · intro j _
    exact (hS.prod hT).prod (lebesgueGridCell_measurable j)
  · intro j _
    exact measure_ne_top W.measure _

theorem latinon_grid_union_difference_le (W V : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (F : Finset (Fin n)) (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcell : ∀ j : Fin n,
      |W.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)-
        V.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)| ≤ delta) :
    |W.measure.real ((S ×ˢ T) ×ˢ symbolGridUnion F)-
      V.measure.real ((S ×ˢ T) ×ˢ symbolGridUnion F)| ≤ (n : ℝ)*delta := by
  rw [latinon_box_grid_union_sum W hn F S T hS hT,
    latinon_box_grid_union_sum V hn F S T hS hT,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ F, |W.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)-
        V.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ F, delta := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (F.card : ℝ)*delta := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (n : ℝ)*delta := by
      apply mul_le_mul_of_nonneg_right _ hdelta
      exact_mod_cast (show F.card ≤ n by simpa using F.card_le_univ)

/-- Finitely many symbol-slice cut tests control the FULL distribution cut
norm,uniformly over all Latinons,including singular ones. -/
theorem measureCut_le_symbol_grid_tests (W V : LatinonMeasure) {n : ℕ} (hn : 0 < n)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcell : ∀ j : Fin n, ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
      |W.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)-
        V.measure.real ((S ×ˢ T) ×ˢ lebesgueGridCell j)| ≤ delta) :
    measureCut W.measure V.measure ≤ (n : ℝ)*delta+4/(n : ℝ) := by
  apply cutValueSup_le
  intro B
  obtain ⟨F,hsub,herr⟩ := symbol_grid_inner_approximation_error hn B.symbols B.symbols_interval
  have hW := (latinon_box_inner_symbol_error W B.rows B.cols B.symbols (symbolGridUnion F)
    B.symbols_measurable (symbolGridUnion_measurable F) hsub).trans herr
  have hV := (latinon_box_inner_symbol_error V B.rows B.cols B.symbols (symbolGridUnion F)
    B.symbols_measurable (symbolGridUnion_measurable F) hsub).trans herr
  have hM := latinon_grid_union_difference_le W V hn F B.rows B.cols B.rows_measurable
    B.cols_measurable delta hdelta (fun j => hcell j _ _ B.rows_measurable B.cols_measurable)
  have htri := (abs_sub_le (W.measure.real B.carrier)
    (W.measure.real ((B.rows ×ˢ B.cols) ×ˢ symbolGridUnion F)) (V.measure.real B.carrier)).trans
    (add_le_add le_rfl (abs_sub_le (W.measure.real ((B.rows ×ˢ B.cols) ×ˢ symbolGridUnion F))
      (V.measure.real ((B.rows ×ˢ B.cols) ×ˢ symbolGridUnion F)) (V.measure.real B.carrier)))
  rw [abs_sub_comm (V.measure.real ((B.rows ×ˢ B.cols) ×ˢ symbolGridUnion F))] at htri
  change |W.measure.real ((B.rows ×ˢ B.cols) ×ˢ B.symbols)-
    V.measure.real ((B.rows ×ˢ B.cols) ×ˢ B.symbols)| ≤ _
  dsimp only [LatinonBox.carrier] at htri
  calc
    _ ≤ _ := htri
    _ ≤ 2/(n : ℝ)+((n : ℝ)*delta+2/(n : ℝ)) := add_le_add hW (add_le_add hM hV)
    _ = _ := by ring

end LatinonEntropy

#print axioms LatinonEntropy.latinon_box_inner_symbol_error
#print axioms LatinonEntropy.latinon_box_grid_union_sum
#print axioms LatinonEntropy.latinon_grid_union_difference_le
#print axioms LatinonEntropy.measureCut_le_symbol_grid_tests
