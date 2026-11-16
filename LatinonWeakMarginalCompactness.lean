module

public import LatinonSymbolCompression
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Filter Topology
open scoped Classical unitInterval

def latinonXZProjection (p : LatinonPoint) : I × I := (p.1.1,p.2)
def latinonYZProjection (p : LatinonPoint) : I × I := (p.1.2,p.2)

theorem latinon_xz_preserving (W : LatinonMeasure) :
    MeasurePreserving latinonXZProjection W.measure unitSquareVolume := by
  have hm : Measurable latinonXZProjection :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  refine ⟨hm,?_⟩
  apply Measure.ext_prod
  intro S T hS hT
  rw [Measure.map_apply hm (hS.prod hT),Measure.prod_prod]
  have he : latinonXZProjection ⁻¹' (S ×ˢ T) = (S ×ˢ Set.univ) ×ˢ T := by
    ext p
    simp only [latinonXZProjection,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
  rw [he,W.xz_uniform S T hS hT]

theorem latinon_yz_preserving (W : LatinonMeasure) :
    MeasurePreserving latinonYZProjection W.measure unitSquareVolume := by
  have hm : Measurable latinonYZProjection :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  refine ⟨hm,?_⟩
  apply Measure.ext_prod
  intro S T hS hT
  rw [Measure.map_apply hm (hS.prod hT),Measure.prod_prod]
  have he : latinonYZProjection ⁻¹' (S ×ˢ T) = (Set.univ ×ˢ S) ×ˢ T := by
    ext p
    simp only [latinonYZProjection,Set.mem_preimage,Set.mem_prod,Set.mem_univ,true_and]
  rw [he,W.yz_uniform S T hS hT]

def latinonProbability (W : LatinonMeasure) : ProbabilityMeasure LatinonPoint :=
  W.measure.toProbabilityMeasure

def squareProbability : ProbabilityMeasure (I × I) := unitSquareVolume.toProbabilityMeasure

/-- Distributional marginals in the WEAK probability-measure topology.
This set does not encode the full Latinon metric or its order term. -/
def uniformPairProbabilitySet : Set (ProbabilityMeasure LatinonPoint) :=
  {nu | nu.map Prod.fst=squareProbability ∧
    nu.map latinonXZProjection=squareProbability ∧ nu.map latinonYZProjection=squareProbability}

theorem uniformPairProbabilitySet_closed : IsClosed uniformPairProbabilitySet := by
  have hxy : Continuous (fun nu : ProbabilityMeasure LatinonPoint => nu.map Prod.fst) :=
    ProbabilityMeasure.continuous_map continuous_fst
  have hxz : Continuous (fun nu : ProbabilityMeasure LatinonPoint => nu.map latinonXZProjection) :=
    ProbabilityMeasure.continuous_map ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hyz : Continuous (fun nu : ProbabilityMeasure LatinonPoint => nu.map latinonYZProjection) :=
    ProbabilityMeasure.continuous_map ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact (isClosed_eq hxy continuous_const).inter
    ((isClosed_eq hxz continuous_const).inter (isClosed_eq hyz continuous_const))

theorem uniformPairProbabilitySet_compact : IsCompact uniformPairProbabilitySet :=
  uniformPairProbabilitySet_closed.isCompact

theorem latinonProbability_mem_uniformPairProbabilitySet (W : LatinonMeasure) :
    latinonProbability W ∈ uniformPairProbabilitySet := by
  refine ⟨?_,?_,?_⟩
  · apply Subtype.ext
    exact (latinon_xy_preserving W).map_eq
  · apply Subtype.ext
    exact (latinon_xz_preserving W).map_eq
  · apply Subtype.ext
    exact (latinon_yz_preserving W).map_eq

/-- A weakly convergent subsequence with all three uniform pair margins.
Full cut convergence still requires alignment and a cut-Cauchy argument. -/
theorem exists_weak_subsequence_uniform_pair_margins (W : ℕ → LatinonMeasure) :
    ∃ nu ∈ uniformPairProbabilitySet, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => latinonProbability (W (phi n))) atTop (𝓝 nu) :=
  uniformPairProbabilitySet_compact.tendsto_subseq
    (fun n => latinonProbability_mem_uniformPairProbabilitySet (W n))

end LatinonEntropy

#print axioms LatinonEntropy.latinon_xz_preserving
#print axioms LatinonEntropy.latinon_yz_preserving
#print axioms LatinonEntropy.uniformPairProbabilitySet_closed
#print axioms LatinonEntropy.uniformPairProbabilitySet_compact
#print axioms LatinonEntropy.latinonProbability_mem_uniformPairProbabilitySet
#print axioms LatinonEntropy.exists_weak_subsequence_uniform_pair_margins
