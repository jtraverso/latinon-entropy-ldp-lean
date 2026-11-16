module

public import LebesgueGridPartition
public import LatinSymbolIntervalBlocks

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

/-- The interval table obtained from actual intersections with the aligned grid.
Its identification with the integral of a finite Latinon is a separate step. -/
def alignedLatinIntervalTable {n r s t : ℕ} (P : SymbolIntervalPartition t)
    (A : MeasurableFinitePartition (volume : Measure I) r)
    (B : MeasurableFinitePartition (volume : Measure I) s)
    (phi psi : I → I) (L : LatinArray n) (z : LatinBlock r s t) : ℝ :=
  latinIntervalFractionalTable P (lebesgueAlignmentWeight A phi) (lebesgueAlignmentWeight B psi) L z

/-- The order threshold precedes all measurable partitions, alignments and
squares. Neither stochastic matrices nor their margins are assumed as data. -/
theorem exists_uniform_measurable_interval_rounding {t : ℕ} (P : SymbolIntervalPartition t)
    (r s : ℕ) (tau : ℝ) (htau : 0 < tau) (M : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (A : MeasurableFinitePartition (volume : Measure I) r)
        (B : MeasurableFinitePartition (volume : Measure I) s) (phi psi : I → I),
      MeasurePreserving phi volume volume → MeasurePreserving psi volume volume →
      ∀ L : LatinArray n, ∃ (row : Fin n → Fin r) (col : Fin n → Fin s),
        (∀ z : LatinBlock r s t,
          |latinBlockObservable row col (P.color n) z L/(n : ℝ)^2-
            alignedLatinIntervalTable P A B phi psi L z| < tau) ∧
        (∀ a, |((univ.filter (fun x => row x = a)).card : ℝ)/(n : ℝ)-volume.real (A.cell a)| < tau) ∧
        (∀ b, |((univ.filter (fun y => col y = b)).card : ℝ)/(n : ℝ)-volume.real (B.cell b)| < tau) ∧
        (∀ a : Fin n, (M : ℝ)^2 ≤ ((symbolColorFiber (P.color n) a).card : ℝ)) := by
  obtain ⟨N,hN,hround⟩ := exists_uniform_latin_interval_rounding P r s tau htau M
  refine ⟨N,hN,?_⟩
  intro n hn A B phi psi hphi hpsi L
  have hnpos : 0 < n := hN.trans_le hn
  obtain ⟨hp,hpt,hpm⟩ := lebesgue_alignment_weights_stochastic_and_means hnpos A phi hphi
  obtain ⟨hq,hqt,hqm⟩ := lebesgue_alignment_weights_stochastic_and_means hnpos B psi hpsi
  obtain ⟨row,col,hb,hr,hc,hsize⟩ := hround n hn
    (lebesgueAlignmentWeight A phi) (lebesgueAlignmentWeight B psi) hp hq hpt hqt L
  refine ⟨row,col,hb,?_,?_,hsize⟩
  · intro a
    simpa only [hpm a] using hr a
  · intro b
    simpa only [hqm b] using hc b

example : (∑ a : Fin 1, lebesgueAlignmentWeight
    (lebesgueGridPartition 1 (by decide)) id (0 : Fin 1) a) = 1 := by
  exact (lebesgue_alignment_weights_stochastic_and_means (n := 1) (by decide)
    (lebesgueGridPartition 1 (by decide)) id (MeasurePreserving.id volume)).2.1 0

end LatinonEntropy

#print axioms LatinonEntropy.exists_uniform_measurable_interval_rounding
#print axioms LatinonEntropy.MeasurableFinitePartition.sum_real_inter
#print axioms LatinonEntropy.MeasurableFinitePartition.sum_real_inter_left
#print axioms LatinonEntropy.MeasurableFinitePartition.pullback
#print axioms LatinonEntropy.alignedPartitionWeight_nonneg
#print axioms LatinonEntropy.alignedPartitionWeight_row
#print axioms LatinonEntropy.alignedPartitionWeight_mean
#print axioms LatinonEntropy.aligned_partition_weights_stochastic_and_means
#print axioms LatinonEntropy.lebesgueGridCell_measurable
#print axioms LatinonEntropy.lebesgueGridCell_mass
#print axioms LatinonEntropy.lebesgueGridCell_disjoint
#print axioms LatinonEntropy.lebesgueGridCell_cover_positive
#print axioms LatinonEntropy.lebesgueGridCell_cover_ae
#print axioms LatinonEntropy.lebesgueGridPartition
#print axioms LatinonEntropy.lebesgue_alignment_weights_stochastic_and_means
