module

/- Local application and axiom audit of the pinned Graphon regularity theorem. -/
public import Graphon.Regularity
public import LatinonBridge.BipartiteKernel

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

/-- Weak regularity applies to an actual directed bounded kernel through its
two tagged off-diagonal blocks. No symmetry of the original kernel is assumed. -/
theorem exists_bipartite_regular_partition (g : I × I → ℝ) (hg : Measurable g)
    (hb : ∀ᵐ p ∂(volume.prod volume : Measure (I × I)), g p ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ P : MeasurablePartition BipartiteSpace bipartiteVolume,
      P.parts.card ≤ Graphon.regularityBound eps ∧
      Graphon.cutNormDiff (bipartiteGraphon g hg hb)
        (Graphon.stepify P (bipartiteGraphon g hg hb)) ≤ eps :=
  Graphon.regularity (bipartiteGraphon g hg hb) eps heps

end LatinonEntropy

#print axioms LatinonEntropy.exists_bipartite_regular_partition
#print axioms Graphon.regularity
#print axioms Graphon.exists_equipartition_almost_refining
#print axioms Graphon.MeasurePreserving.exists_controlled_cell_alignment
