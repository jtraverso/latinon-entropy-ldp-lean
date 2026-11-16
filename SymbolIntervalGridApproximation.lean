module

public import LebesgueGridPartition
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

def symbolGridUnion {n : ℕ} (F : Finset (Fin n)) : Set I := ⋃ i ∈ F, lebesgueGridCell i

theorem symbolGridUnion_measurable {n : ℕ} (F : Finset (Fin n)) : MeasurableSet (symbolGridUnion F) :=
  MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => lebesgueGridCell_measurable i))

theorem lebesgueGridCell_point_lt {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i < j)
    {x y : I} (hx : x ∈ lebesgueGridCell i) (hy : y ∈ lebesgueGridCell j) : x < y :=
  (hx.2.trans (lebesgueGrid_separation hn hij)).trans_lt hy.1

/-- Every order-connected symbol set has a union of whole grid cells inside
it. The omitted portion lies in at most two cells and the null point zero. -/
theorem exists_symbol_grid_inner_approximation {n : ℕ} (hn : 0 < n)
    (U : Set I) (hU : U.OrdConnected) :
    ∃ F : Finset (Fin n), ∃ lo hi : Fin n,
      symbolGridUnion F ⊆ U ∧
      U \ symbolGridUnion F ⊆ ({0} ∪ lebesgueGridCell lo) ∪ lebesgueGridCell hi := by
  let occupied : Finset (Fin n) := univ.filter (fun i => ∃ u ∈ U, u ∈ lebesgueGridCell i)
  by_cases hocc : occupied.Nonempty
  · let lo := occupied.min' hocc
    let hi := occupied.max' hocc
    let F : Finset (Fin n) := univ.filter (fun i => lo < i ∧ i < hi)
    have hlo : lo ∈ occupied := Finset.min'_mem occupied hocc
    have hhi : hi ∈ occupied := Finset.max'_mem occupied hocc
    obtain ⟨x,hxU,hxlo⟩ := (Finset.mem_filter.mp hlo).2
    obtain ⟨y,hyU,hyhi⟩ := (Finset.mem_filter.mp hhi).2
    refine ⟨F,lo,hi,?_,?_⟩
    · intro z hz
      obtain ⟨i,hzi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hiF,hzi⟩ := Set.mem_iUnion.mp hzi
      have hbetween := (Finset.mem_filter.mp hiF).2
      exact hU.out hxU hyU ⟨(lebesgueGridCell_point_lt hn hbetween.1 hxlo hzi).le,
        (lebesgueGridCell_point_lt hn hbetween.2 hzi hyhi).le⟩
    · intro z hz
      by_cases hz0 : z=0
      · exact Or.inl (Or.inl hz0)
      · have hne : (z : ℝ) ≠ 0 := fun he => hz0 (Subtype.ext he)
        have hpos : 0 < (z : ℝ) := lt_of_le_of_ne z.property.1 hne.symm
        obtain ⟨i,hzi⟩ := lebesgueGridCell_cover_positive hn z hpos
        have hiocc : i ∈ occupied := Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨z,hz.1,hzi⟩⟩
        have hli : lo ≤ i := Finset.min'_le occupied i hiocc
        have hih : i ≤ hi := Finset.le_max' occupied i hiocc
        by_cases hil : i=lo
        · exact Or.inl (Or.inr (hil ▸ hzi))
        · by_cases hih' : i=hi
          · exact Or.inr (hih' ▸ hzi)
          · exfalso
            apply hz.2
            apply Set.mem_iUnion.mpr ⟨i,?_⟩
            exact Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              lt_of_le_of_ne hli (fun he => hil he.symm),lt_of_le_of_ne hih hih'⟩,hzi⟩
  · refine ⟨∅,⟨0,hn⟩,⟨0,hn⟩,?_,?_⟩
    · simp [symbolGridUnion]
    · intro z hz
      by_cases hz0 : z=0
      · exact Or.inl (Or.inl hz0)
      · have hne : (z : ℝ) ≠ 0 := fun he => hz0 (Subtype.ext he)
        have hpos : 0 < (z : ℝ) := lt_of_le_of_ne z.property.1 hne.symm
        obtain ⟨i,hzi⟩ := lebesgueGridCell_cover_positive hn z hpos
        exact False.elim (hocc ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨z,hz.1,hzi⟩⟩⟩)

theorem symbol_grid_inner_approximation_error {n : ℕ} (hn : 0 < n)
    (U : Set I) (hU : U.OrdConnected) :
    ∃ F : Finset (Fin n), symbolGridUnion F ⊆ U ∧
      (volume : Measure I).real (U \ symbolGridUnion F) ≤ 2/(n : ℝ) := by
  obtain ⟨F,lo,hi,hsub,hboundary⟩ := exists_symbol_grid_inner_approximation hn U hU
  refine ⟨F,hsub,?_⟩
  calc
    (volume : Measure I).real (U \ symbolGridUnion F) ≤
        volume.real (({0} ∪ lebesgueGridCell lo) ∪ lebesgueGridCell hi) := measureReal_mono hboundary
    _ ≤ volume.real ({0} ∪ lebesgueGridCell lo)+volume.real (lebesgueGridCell hi) :=
      measureReal_union_le _ _
    _ ≤ (volume.real {0}+volume.real (lebesgueGridCell lo))+volume.real (lebesgueGridCell hi) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ = 2/(n : ℝ) := by
      rw [lebesgueGridCell_mass hn lo,lebesgueGridCell_mass hn hi]
      have hzero : (volume : Measure I).real {0}=0 := by simp [measureReal_def]
      rw [hzero]
      ring

end LatinonEntropy

#print axioms LatinonEntropy.symbolGridUnion_measurable
#print axioms LatinonEntropy.lebesgueGridCell_point_lt
#print axioms LatinonEntropy.exists_symbol_grid_inner_approximation
#print axioms LatinonEntropy.symbol_grid_inner_approximation_error
