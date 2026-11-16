module

public import LatinonFiniteSymbolGrid

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

theorem unitGridIndex_monotone (n : ℕ) (hn : 0 < n) : Monotone (unitGridIndex n hn) := by
  intro x y hxy
  by_cases he : x=y
  · subst y
    exact le_refl _
  · by_contra hi
    have hsep := lebesgueGrid_separation hn (lt_of_not_ge hi)
    have hx := unitGridIndex_location n hn x
    have hy := unitGridIndex_location n hn y
    have hrev : (y : ℝ) ≤ (x : ℝ) := (hy.2.trans hsep).trans hx.1
    have hlt : x < y := lt_of_le_of_ne hxy he
    exact (not_lt_of_ge hrev) hlt

theorem unitGridIndex_strict_reflect (n : ℕ) (hn : 0 < n) {x y : I}
    (h : unitGridIndex n hn x < unitGridIndex n hn y) : x < y := by
  apply lt_of_not_ge
  intro hyx
  exact (not_le_of_gt h) (unitGridIndex_monotone n hn hyx)

def finiteGridIndexLaw (n : ℕ) (hn : 0 < n) : Measure (Fin n) :=
  (volume : Measure I).map (unitGridIndex n hn)

instance finiteGridIndexLaw_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (finiteGridIndexLaw n hn) := by
  refine ⟨?_⟩
  rw [finiteGridIndexLaw,Measure.map_apply (unitGridIndex_measurable n hn) MeasurableSet.univ,
    Set.preimage_univ,measure_univ]

theorem unitGridIndex_preserving (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (unitGridIndex n hn) (volume : Measure I) (finiteGridIndexLaw n hn) :=
  ⟨unitGridIndex_measurable n hn,rfl⟩

theorem finiteGridIndexLaw_real_atom (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (finiteGridIndexLaw n hn).real {i}=1/(n : ℝ) := by
  have h := congrArg ENNReal.toReal (finiteCellIndex_map_cell (volume : Measure I)
    lebesgueGridCell ⟨0,hn⟩ lebesgueGridCell_measurable (lebesgueGridCell_disjoint hn)
    (lebesgueGridCell_cover_ae hn) i)
  exact h.trans (lebesgueGridCell_mass hn i)

abbrev FinitePatternConfig (n k l : ℕ) := (Fin k → Fin n) × (Fin l → Fin n)

def finitePatternIndexLaw (n : ℕ) (hn : 0 < n) (k l : ℕ) : Measure (FinitePatternConfig n k l) :=
  (Measure.pi (fun _ : Fin k => finiteGridIndexLaw n hn)).prod
    (Measure.pi (fun _ : Fin l => finiteGridIndexLaw n hn))

instance finitePatternIndexLaw_probability (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    IsProbabilityMeasure (finitePatternIndexLaw n hn k l) := by
  unfold finitePatternIndexLaw
  infer_instance

def patternConfigGridIndices {k l : ℕ} (n : ℕ) (hn : 0 < n)
    (c : LatinonPatternConfig k l) : FinitePatternConfig n k l :=
  (fun i => unitGridIndex n hn (c.1 i),fun j => unitGridIndex n hn (c.2 j))

theorem patternConfigGridIndices_preserving (n : ℕ) (hn : 0 < n) (k l : ℕ) :
    MeasurePreserving (patternConfigGridIndices (k := k) (l := l) n hn)
      (latinonPatternConfigLaw k l) (finitePatternIndexLaw n hn k l) :=
  (measurePreserving_pi (fun _ : Fin k => (volume : Measure I))
    (fun _ : Fin k => finiteGridIndexLaw n hn) (fun _ => unitGridIndex_preserving n hn)).prod
  (measurePreserving_pi (fun _ : Fin l => (volume : Measure I))
    (fun _ : Fin l => finiteGridIndexLaw n hn) (fun _ => unitGridIndex_preserving n hn))

theorem finitePatternIndexLaw_real_atom (n : ℕ) (hn : 0 < n) (k l : ℕ)
    (c : FinitePatternConfig n k l) :
    (finitePatternIndexLaw n hn k l).real {c}=(1/(n : ℝ))^(k+l) := by
  have hs : ({c} : Set (FinitePatternConfig n k l))={c.1} ×ˢ {c.2} := by
    exact (Set.singleton_prod_singleton).symm
  rw [hs,finitePatternIndexLaw,measureReal_prod_prod]
  simp only [Measure.real,Measure.pi_singleton,ENNReal.toReal_prod]
  change (∏ _i : Fin k, (finiteGridIndexLaw n hn).real {c.1 _i})*
    (∏ _j : Fin l, (finiteGridIndexLaw n hn).real {c.2 _j})=_
  simp only [finiteGridIndexLaw_real_atom,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (pow_add _ _ _).symm

def finiteMatrixPatternConfigs {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Set (FinitePatternConfig n k l) :=
  {c | StrictMono c.1 ∧ StrictMono c.2 ∧ ∀ a b, P a < P b →
    L.val (c.1 a.1) (c.2 a.2) < L.val (c.1 b.1) (c.2 b.2)}

def finiteMatrixPatternFamily {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) :
    Finset (FinitePatternConfig n k l) := Finset.univ.filter (fun c => c ∈ finiteMatrixPatternConfigs L P)

/-- An explicit matrix count with the same k!l!/n^(k+l) coordinate
normalization as raw Latinon sampling. No embedding enters this definition. -/
def finiteMatrixPatternDensity {n k l : ℕ} (L : LatinArray n) (P : LatinOrderPattern k l) : ℝ :=
  ((k.factorial*l.factorial : ℕ) : ℝ)*((finiteMatrixPatternFamily L P).card : ℝ)/(n : ℝ)^(k+l)

theorem finiteMatrixPatternDensity_eq_config_probability {n k l : ℕ} (hn : 0 < n)
    (L : LatinArray n) (P : LatinOrderPattern k l) :
    finiteMatrixPatternDensity L P=((k.factorial*l.factorial : ℕ) : ℝ)*
      (latinonPatternConfigLaw k l).real
        ((patternConfigGridIndices n hn) ⁻¹' finiteMatrixPatternConfigs L P) := by
  have hm := patternConfigGridIndices_preserving n hn k l
  rw [hm.measureReal_preimage (Set.toFinite (finiteMatrixPatternConfigs L P)).measurableSet.nullMeasurableSet]
  have he : finiteMatrixPatternConfigs L P=
      ⋃ c ∈ finiteMatrixPatternFamily L P, ({c} : Set (FinitePatternConfig n k l)) := by
    ext c
    simp only [Set.mem_iUnion,Set.mem_singleton_iff,finiteMatrixPatternFamily,
      Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [he]
  have hdisj : Set.PairwiseDisjoint (↑(finiteMatrixPatternFamily L P))
      (fun c : FinitePatternConfig n k l => ({c} : Set (FinitePatternConfig n k l))) := by
    intro c _ d _ hcd
    exact Set.disjoint_singleton.mpr hcd
  rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_singleton _)]
  simp only [finitePatternIndexLaw_real_atom,Finset.sum_const,nsmul_eq_mul]
  unfold finiteMatrixPatternDensity
  rw [one_div,inv_pow,div_eq_mul_inv]
  ring

end LatinonEntropy

#print axioms LatinonEntropy.unitGridIndex_monotone
#print axioms LatinonEntropy.unitGridIndex_strict_reflect
#print axioms LatinonEntropy.finiteGridIndexLaw_probability
#print axioms LatinonEntropy.unitGridIndex_preserving
#print axioms LatinonEntropy.finiteGridIndexLaw_real_atom
#print axioms LatinonEntropy.finitePatternIndexLaw_probability
#print axioms LatinonEntropy.patternConfigGridIndices_preserving
#print axioms LatinonEntropy.finitePatternIndexLaw_real_atom
#print axioms LatinonEntropy.finiteMatrixPatternDensity_eq_config_probability
