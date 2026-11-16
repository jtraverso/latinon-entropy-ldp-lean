module

public import FiniteAverages
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical

/-- A finite measurable partition, allowing a null exceptional set. -/
structure MeasurableFinitePartition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : ℕ) where
  cell : Fin q → Set α
  measurable : ∀ i, MeasurableSet (cell i)
  disjoint : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)
  cover : ∀ᵐ x ∂μ, ∃ i, x ∈ cell i

namespace MeasurableFinitePartition

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℕ}

theorem sum_real_inter [IsFiniteMeasure μ] (A : MeasurableFinitePartition μ q)
    (B : Set α) (hB : MeasurableSet B) :
    (∑ i, μ.real (A.cell i ∩ B)) = μ.real B := by
  have hd : Pairwise (fun i j => Disjoint (A.cell i ∩ B) (A.cell j ∩ B)) := by
    intro i j hij
    exact (A.disjoint i j hij).mono Set.inter_subset_left Set.inter_subset_left
  have he : (⋃ i, A.cell i ∩ B) =ᵐ[μ] B := by
    filter_upwards [A.cover] with x hx
    apply propext
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · rintro ⟨i,_,hxB⟩
      exact hxB
    · intro hxB
      obtain ⟨i,hi⟩ := hx
      exact ⟨i,hi,hxB⟩
  exact (measureReal_iUnion_fintype (μ := μ) hd (fun i => (A.measurable i).inter hB)).symm.trans
    (measureReal_congr he)

theorem sum_real_inter_left [IsFiniteMeasure μ] (A : MeasurableFinitePartition μ q)
    (B : Set α) (hB : MeasurableSet B) :
    (∑ i, μ.real (B ∩ A.cell i)) = μ.real B := by
  simp_rw [Set.inter_comm B]
  exact A.sum_real_inter B hB

def pullback (A : MeasurableFinitePartition μ q) (phi : α → α)
    (hphi : MeasurePreserving phi μ μ) : MeasurableFinitePartition μ q where
  cell := fun i => phi ⁻¹' A.cell i
  measurable := fun i => (A.measurable i).preimage hphi.measurable
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (A.disjoint i j hij) hxi hxj
  cover := hphi.quasiMeasurePreserving.ae A.cover

end MeasurableFinitePartition

/-- The weights extracted from an actual measure-preserving alignment. -/
def alignedPartitionWeight {α : Type*} [MeasurableSpace α] {μ : Measure α} {n r : ℕ}
    (G : MeasurableFinitePartition μ n) (A : MeasurableFinitePartition μ r)
    (phi : α → α) (i : Fin n) (a : Fin r) : ℝ :=
  (n : ℝ)*μ.real (A.cell a ∩ phi ⁻¹' G.cell i)

theorem alignedPartitionWeight_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n r : ℕ} (G : MeasurableFinitePartition μ n)
    (A : MeasurableFinitePartition μ r) (phi : α → α) (i : Fin n) (a : Fin r) :
    0 ≤ alignedPartitionWeight G A phi i a :=
  mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg

theorem alignedPartitionWeight_row {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {n r : ℕ} (hn : 0 < n)
    (G : MeasurableFinitePartition μ n) (A : MeasurableFinitePartition μ r)
    (hG : ∀ i, μ.real (G.cell i) = 1/(n : ℝ))
    (phi : α → α) (hphi : MeasurePreserving phi μ μ) (i : Fin n) :
    (∑ a, alignedPartitionWeight G A phi i a) = 1 := by
  unfold alignedPartitionWeight
  rw [← mul_sum,A.sum_real_inter _ ((G.measurable i).preimage hphi.measurable),
    hphi.measureReal_preimage (G.measurable i).nullMeasurableSet,hG i]
  field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']

theorem alignedPartitionWeight_mean {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {n r : ℕ} (hn : 0 < n)
    (G : MeasurableFinitePartition μ n) (A : MeasurableFinitePartition μ r)
    (phi : α → α) (hphi : MeasurePreserving phi μ μ) (a : Fin r) :
    (∑ i, alignedPartitionWeight G A phi i a)/(n : ℝ) = μ.real (A.cell a) := by
  have hs := (G.pullback phi hphi).sum_real_inter_left (A.cell a) (A.measurable a)
  change (∑ i, μ.real (A.cell a ∩ phi ⁻¹' G.cell i)) = μ.real (A.cell a) at hs
  unfold alignedPartitionWeight
  rw [← mul_sum]
  calc
    _ = ∑ i, μ.real (A.cell a ∩ phi ⁻¹' G.cell i) := by
      field_simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
    _ = _ := hs

theorem aligned_partition_weights_stochastic_and_means {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {n r : ℕ} (hn : 0 < n)
    (G : MeasurableFinitePartition μ n) (A : MeasurableFinitePartition μ r)
    (hG : ∀ i, μ.real (G.cell i) = 1/(n : ℝ))
    (phi : α → α) (hphi : MeasurePreserving phi μ μ) :
    (∀ i a, 0 ≤ alignedPartitionWeight G A phi i a) ∧
      (∀ i, ∑ a, alignedPartitionWeight G A phi i a = 1) ∧
      (∀ a, (∑ i, alignedPartitionWeight G A phi i a)/(n : ℝ) = μ.real (A.cell a)) :=
  ⟨alignedPartitionWeight_nonneg G A phi,alignedPartitionWeight_row hn G A hG phi hphi,
    alignedPartitionWeight_mean hn G A phi hphi⟩

end LatinonEntropy

#print axioms LatinonEntropy.MeasurableFinitePartition.sum_real_inter
#print axioms LatinonEntropy.MeasurableFinitePartition.sum_real_inter_left
#print axioms LatinonEntropy.MeasurableFinitePartition.pullback
#print axioms LatinonEntropy.alignedPartitionWeight_nonneg
#print axioms LatinonEntropy.alignedPartitionWeight_row
#print axioms LatinonEntropy.alignedPartitionWeight_mean
#print axioms LatinonEntropy.aligned_partition_weights_stochastic_and_means
