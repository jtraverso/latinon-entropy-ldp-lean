module

public import FiniteMeasureKL
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical ENNReal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- A total classifier; the uncovered null set goes to the fallback cell. -/
def finiteCellIndex (cell : ι → Set α) (fallback : ι) (x : α) : ι :=
  if h : ∃ i, x ∈ cell i then Classical.choose h else fallback

omit [MeasurableSpace α] in
theorem finiteCellIndex_of_mem (cell : ι → Set α) (fallback : ι)
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) {x : α} {i : ι} (hi : x ∈ cell i) :
    finiteCellIndex cell fallback x = i := by
  have hx : ∃ j, x ∈ cell j := ⟨i,hi⟩
  rw [finiteCellIndex,dite_eq_left hx]
  by_contra hne
  exact Set.disjoint_left.mp (hd _ _ hne) (Classical.choose_spec hx) hi

omit [MeasurableSpace α] in
theorem finiteCellIndex_eq_iff_of_covered (cell : ι → Set α) (fallback : ι)
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) {x : α}
    (hx : ∃ i, x ∈ cell i) (i : ι) :
    finiteCellIndex cell fallback x = i ↔ x ∈ cell i := by
  constructor
  · intro he
    obtain ⟨j,hj⟩ := hx
    have hji : j = i := (finiteCellIndex_of_mem cell fallback hd hj).symm.trans he
    exact hji ▸ hj
  · intro hi
    exact finiteCellIndex_of_mem cell fallback hd hi

omit [MeasurableSpace α] in
theorem finiteCellIndex_fiber (cell : ι → Set α) (fallback : ι)
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) (i : ι) :
    finiteCellIndex cell fallback ⁻¹' {i} =
      if i = fallback then cell i ∪ (⋃ j, cell j)ᶜ else cell i := by
  by_cases hi : i = fallback
  · subst i
    rw [ite_eq_left rfl]
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_union,Set.mem_compl_iff,Set.mem_iUnion]
    by_cases hx : ∃ j, x ∈ cell j
    · simp only [hx,not_true_eq_false,or_false]
      exact finiteCellIndex_eq_iff_of_covered cell fallback hd hx fallback
    · simp only [hx,not_false_eq_true,or_true,iff_true]
      exact dite_eq_right hx
  · rw [ite_eq_right hi]
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    by_cases hx : ∃ j, x ∈ cell j
    · exact finiteCellIndex_eq_iff_of_covered cell fallback hd hx i
    · have hindex : finiteCellIndex cell fallback x = fallback := dite_eq_right hx
      constructor
      · intro he
        exact False.elim (hi (he.symm.trans hindex))
      · intro hm
        exact False.elim (hx ⟨i,hm⟩)

theorem finiteCellIndex_measurable [MeasurableSpace ι] (cell : ι → Set α) (fallback : ι)
    (hc : ∀ i, MeasurableSet (cell i))
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) :
    Measurable (finiteCellIndex cell fallback) := by
  apply measurable_to_countable'
  intro i
  rw [finiteCellIndex_fiber cell fallback hd i]
  split_ifs
  · exact (hc i).union (MeasurableSet.iUnion hc).compl
  · exact hc i

theorem finiteCellIndex_map_cell [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (mu : Measure α) (cell : ι → Set α) (fallback : ι)
    (hc : ∀ i, MeasurableSet (cell i))
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j))
    (hcover : ∀ᵐ x ∂mu, ∃ i, x ∈ cell i) (i : ι) :
    (mu.map (finiteCellIndex cell fallback)) {i} = mu (cell i) := by
  rw [Measure.map_apply (finiteCellIndex_measurable cell fallback hc hd) (measurableSet_singleton i)]
  apply measure_congr
  filter_upwards [hcover] with x hx
  apply propext
  exact finiteCellIndex_eq_iff_of_covered cell fallback hd hx i

/-- A genuine table from measurable cells has relative divergence at most
the original measures' KL. Both null exceptional sets are discharged by
the actual covers, and no bound on the table entropy is an input. -/
theorem finite_cell_table_kl_le [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (mu nu : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (cell : ι → Set α) (fallback : ι) (hc : ∀ i, MeasurableSet (cell i))
    (hd : ∀ i j, i ≠ j → Disjoint (cell i) (cell j))
    (hmu : ∀ᵐ x ∂mu, ∃ i, x ∈ cell i)
    (hnu : ∀ᵐ x ∂nu, ∃ i, x ∈ cell i)
    (hpositive : ∀ i, nu (cell i) ≠ 0) :
    ENNReal.ofReal (-(∑ i, mu.real (cell i)*Real.log (nu.real (cell i)/mu.real (cell i)))) ≤
      InformationTheory.klDiv mu nu := by
  let g := finiteCellIndex cell fallback
  have hg : Measurable g := finiteCellIndex_measurable cell fallback hc hd
  let _ : IsProbabilityMeasure (mu.map g) := ⟨by
    rw [Measure.map_apply hg MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]⟩
  let _ : IsProbabilityMeasure (nu.map g) := ⟨by
    rw [Measure.map_apply hg MeasurableSet.univ]
    simp only [Set.preimage_univ,measure_univ]⟩
  have hp : ∀ i, (nu.map g) {i} ≠ 0 := by
    intro i
    rw [finiteCellIndex_map_cell nu cell fallback hc hd hnu]
    exact hpositive i
  have hmap := InformationTheory.klDiv_map_le (μ := mu) (ν := nu) hg
  rw [finite_probability_kl_eq_neg_table (mu.map g) (nu.map g) hp] at hmap
  have hmr : ∀ i, (mu.map g).real {i} = mu.real (cell i) := fun i =>
    congrArg ENNReal.toReal (finiteCellIndex_map_cell mu cell fallback hc hd hmu i)
  have hnr : ∀ i, (nu.map g).real {i} = nu.real (cell i) := fun i =>
    congrArg ENNReal.toReal (finiteCellIndex_map_cell nu cell fallback hc hd hnu i)
  simp_rw [hmr,hnr] at hmap
  exact hmap

end LatinonEntropy

#print axioms LatinonEntropy.finiteCellIndex_of_mem
#print axioms LatinonEntropy.finiteCellIndex_eq_iff_of_covered
#print axioms LatinonEntropy.finiteCellIndex_fiber
#print axioms LatinonEntropy.finiteCellIndex_measurable
#print axioms LatinonEntropy.finiteCellIndex_map_cell
#print axioms LatinonEntropy.finite_cell_table_kl_le
