module

public import LatinonFinitePatternIndices

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval ProbabilityTheory

theorem latinonPatternSampleLaw_config_preserving (W : LatinonMeasure) (k l : ℕ) :
    MeasurePreserving (Prod.fst : LatinonPatternConfig k l × ((Fin k × Fin l) → I) → LatinonPatternConfig k l)
      (latinonPatternSampleLaw W k l) (latinonPatternConfigLaw k l) := by
  refine ⟨measurable_fst,?_⟩
  exact Measure.fst_compProd _ _

theorem latinonPatternSampleLaw_row_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (i j : Fin k) (hij : i ≠ j) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.1.1 i,p.1.1 j))
      (latinonPatternSampleLaw W k l) unitSquareVolume :=
  ((vertexPair_preserving (Sum.inl i : PatternVertex k l) (Sum.inl j) (by simpa using hij)).comp
    (patternConfigVertices_preserving k l)).comp (latinonPatternSampleLaw_config_preserving W k l)

theorem latinonPatternSampleLaw_col_pair_preserving (W : LatinonMeasure) {k l : ℕ}
    (i j : Fin l) (hij : i ≠ j) :
    MeasurePreserving (fun p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) => (p.1.2 i,p.1.2 j))
      (latinonPatternSampleLaw W k l) unitSquareVolume :=
  ((vertexPair_preserving (Sum.inr i : PatternVertex k l) (Sum.inr j) (by simpa using hij)).comp
    (patternConfigVertices_preserving k l)).comp (latinonPatternSampleLaw_config_preserving W k l)

/-- At the original n-grid resolution the sampled symbols of the
embedded square have exactly the matrix's labels, almost surely. -/
theorem finite_sample_symbol_indices {n k l : ℕ} (hn : 0 < n) (L : LatinArray n) :
    ∀ᵐ p ∂latinonPatternSampleLaw (latinArrayToLatinonMeasure hn L) k l,
      ∀ a : Fin k × Fin l, unitGridIndex n hn (p.2 a)=
        L.val (unitGridIndex n hn (p.1.1 a.1)) (unitGridIndex n hn (p.1.2 a.2)) := by
  let W := latinArrayToLatinonMeasure hn L
  have hK : ∀ᵐ c ∂latinonPatternConfigLaw k l, ∀ a : Fin k × Fin l, ∀ s : Fin n,
      (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real (lebesgueGridCell s)=
        if L.val (unitGridIndex n hn (c.1 a.1)) (unitGridIndex n hn (c.2 a.2))=s then (1 : ℝ) else 0 := by
    apply ae_all_iff.mpr
    intro a
    have hm : MeasurePreserving (fun c : LatinonPatternConfig k l => (c.1 a.1,c.2 a.2))
        (latinonPatternConfigLaw k l) unitSquareVolume :=
      (vertexPair_preserving (Sum.inl a.1 : PatternVertex k l) (Sum.inr a.2) (by simp)).comp
        (patternConfigVertices_preserving k l)
    exact hm.quasiMeasurePreserving.ae (finite_symbol_grid_probability hn L)
  apply ae_all_iff.mpr
  intro a
  let label : LatinonPatternConfig k l → Fin n := fun c =>
    L.val (unitGridIndex n hn (c.1 a.1)) (unitGridIndex n hn (c.2 a.2))
  have hl : Measurable label :=
    (measurable_of_countable (fun v : Fin n × Fin n => L.val v.1 v.2)).comp
      (((unitGridIndex_measurable n hn).comp ((measurable_pi_apply a.1).comp measurable_fst)).prodMk
        ((unitGridIndex_measurable n hn).comp ((measurable_pi_apply a.2).comp measurable_snd)))
  have hp : MeasurableSet {p : LatinonPatternConfig k l × ((Fin k × Fin l) → I) |
      unitGridIndex n hn (p.2 a)=label p.1} :=
    measurableSet_eq_fun ((unitGridIndex_measurable n hn).comp
      ((measurable_pi_apply a).comp measurable_snd)) (hl.comp measurable_fst)
  change ∀ᵐ p ∂(latinonPatternConfigLaw k l ⊗ₘ latinonPatternSymbolKernel W k l),
    unitGridIndex n hn (p.2 a)=label p.1
  apply Measure.ae_compProd_of_ae_ae hp
  filter_upwards [hK] with c hc
  have heval : MeasurePreserving (fun z : (Fin k × Fin l) → I => z a)
      (latinonPatternSymbolKernel W k l c) (latinonSymbolKernel W (c.1 a.1,c.2 a.2)) :=
    measurePreserving_eval (fun d : Fin k × Fin l => latinonSymbolKernel W (c.1 d.1,c.2 d.2)) a
  have hreal : (latinonPatternSymbolKernel W k l c).real
      {z | z a ∈ lebesgueGridCell (label c)}=1 := by
    have h := congrArg ENNReal.toReal (heval.measure_preimage
      (lebesgueGridCell_measurable (label c)).nullMeasurableSet)
    have hcell : (latinonSymbolKernel W (c.1 a.1,c.2 a.2)).real
        (lebesgueGridCell (label c))=1 := by
      simpa only [label,ite_true] using hc a (label c)
    exact h.trans hcell
  have hone : (latinonPatternSymbolKernel W k l c) {z | z a ∈ lebesgueGridCell (label c)}=1 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      (by
        change ((latinonPatternSymbolKernel W k l c)
          {z | z a ∈ lebesgueGridCell (label c)}).toReal=1 at hreal
        simpa only [ENNReal.toReal_one] using hreal)
  have hae : ∀ᵐ z ∂latinonPatternSymbolKernel W k l c, z a ∈ lebesgueGridCell (label c) := by
    rw [ae_iff]
    change (latinonPatternSymbolKernel W k l c) ({z | z a ∈ lebesgueGridCell (label c)}ᶜ)=0
    have hmeas : MeasurableSet {z : (Fin k × Fin l) → I |
        z a ∈ lebesgueGridCell (label c)} :=
      (lebesgueGridCell_measurable (label c)).preimage (measurable_pi_apply a)
    rw [prob_compl_eq_one_sub hmeas,hone,tsub_self]
  exact hae.mono (fun z hz => unitGridIndex_of_mem hn hz)

end LatinonEntropy

#print axioms LatinonEntropy.latinonPatternSampleLaw_config_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_row_pair_preserving
#print axioms LatinonEntropy.latinonPatternSampleLaw_col_pair_preserving
#print axioms LatinonEntropy.finite_sample_symbol_indices
