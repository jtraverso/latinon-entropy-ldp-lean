module

public import MeasurableAlignmentWeights
public import SymbolIntervalWeights
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Order.Interval.Set.Union

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset MeasureTheory
open scoped Classical unitInterval

def lebesgueGridCell {n : ℕ} (z : Fin n) : Set I :=
  ((↑) : I → ℝ) ⁻¹' symbolGridCell z

theorem lebesgueGridCell_measurable {n : ℕ} (z : Fin n) : MeasurableSet (lebesgueGridCell z) :=
  measurableSet_Ioc.preimage measurable_subtype_coe

theorem symbolGridCell_subset_unit {n : ℕ} (hn : 0 < n) (z : Fin n) :
    symbolGridCell z ⊆ Set.Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlo : 0 ≤ symbolGridLower z := div_nonneg (Nat.cast_nonneg z.val) hnR.le
  have hhi : symbolGridUpper z ≤ 1 := by
    unfold symbolGridUpper
    apply (div_le_iff₀ hnR).mpr
    have hz : z.val+1 ≤ n := Nat.succ_le_of_lt z.isLt
    have hzR : (z.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast hz
    simpa only [one_mul] using hzR
  intro x hx
  exact ⟨hlo.trans hx.1.le,hx.2.trans hhi⟩

theorem lebesgueGridCell_image {n : ℕ} (hn : 0 < n) (z : Fin n) :
    ((↑) : I → ℝ) '' lebesgueGridCell z = symbolGridCell z := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact hu
  · intro hx
    exact ⟨⟨x,symbolGridCell_subset_unit hn z hx⟩,hx,rfl⟩

theorem lebesgueGridCell_mass {n : ℕ} (hn : 0 < n) (z : Fin n) :
    (volume : Measure I).real (lebesgueGridCell z) = 1/(n : ℝ) := by
  rw [measureReal_def,unitInterval.volume_apply,lebesgueGridCell_image hn z]
  change (volume (Set.Ioc (symbolGridLower z) (symbolGridUpper z))).toReal = _
  rw [Real.volume_Ioc,ENNReal.toReal_ofReal (symbolGrid_width_nonneg z),symbolGrid_width]

theorem lebesgueGrid_separation {n : ℕ} (hn : 0 < n) {i j : Fin n} (hij : i < j) :
    symbolGridUpper i ≤ symbolGridLower j := by
  unfold symbolGridUpper symbolGridLower
  apply (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).mpr
  have hnat : i.val+1 ≤ j.val := Nat.succ_le_of_lt hij
  exact_mod_cast hnat

theorem lebesgueGridCell_disjoint {n : ℕ} (hn : 0 < n) (i j : Fin n) (hij : i ≠ j) :
    Disjoint (lebesgueGridCell i) (lebesgueGridCell j) := by
  apply Set.disjoint_left.mpr
  intro u hi hj
  change symbolGridLower i < (u : ℝ) ∧ (u : ℝ) ≤ symbolGridUpper i at hi
  change symbolGridLower j < (u : ℝ) ∧ (u : ℝ) ≤ symbolGridUpper j at hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hs := lebesgueGrid_separation hn hlt
    linarith only [hi.2,hj.1,hs]
  · have hs := lebesgueGrid_separation hn hgt
    linarith only [hj.2,hi.1,hs]

theorem lebesgueGridCell_cover_positive {n : ℕ} (hn : 0 < n) (u : I) (hu : 0 < (u : ℝ)) :
    ∃ z : Fin n, u ∈ lebesgueGridCell z := by
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have huI : (u : ℝ) ∈ Set.Ioc (((0 : ℕ) : ℝ)/(n : ℝ)) ((n : ℝ)/(n : ℝ)) := by
    rw [Nat.cast_zero,zero_div,div_self hnR]
    exact ⟨hu,u.property.2⟩
  have hc := Ioc_subset_biUnion_Ioc n (fun k : ℕ => (k : ℝ)/(n : ℝ)) huI
  simp only [Set.mem_iUnion] at hc
  obtain ⟨k,hk,hku⟩ := hc
  refine ⟨⟨k,mem_range.mp hk⟩,?_⟩
  change (k : ℝ)/(n : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((k : ℝ)+1)/(n : ℝ)
  simpa only [Set.mem_Ioc,Nat.cast_add,Nat.cast_one] using hku

theorem lebesgueGridCell_cover_ae {n : ℕ} (hn : 0 < n) :
    ∀ᵐ u : I ∂volume, ∃ z : Fin n, u ∈ lebesgueGridCell z := by
  filter_upwards [(volume : Measure I).ae_ne (0 : I)] with u hu
  have hne : (u : ℝ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 hne.symm
  exact lebesgueGridCell_cover_positive hn u hpos

/-- The actual uniform Lebesgue grid, covering the closed unit interval a.e. -/
def lebesgueGridPartition (n : ℕ) (hn : 0 < n) :
    MeasurableFinitePartition (volume : Measure I) n where
  cell := lebesgueGridCell
  measurable := lebesgueGridCell_measurable
  disjoint := lebesgueGridCell_disjoint hn
  cover := lebesgueGridCell_cover_ae hn

def lebesgueAlignmentWeight {n r : ℕ}
    (A : MeasurableFinitePartition (volume : Measure I) r) (phi : I → I)
    (i : Fin n) (a : Fin r) : ℝ :=
  (n : ℝ)*volume.real (A.cell a ∩ phi ⁻¹' lebesgueGridCell i)

/-- Stochasticity and the exact class means follow from the actual uniform
grid and measure preservation; no matrix margins are assumed. -/
theorem lebesgue_alignment_weights_stochastic_and_means {n r : ℕ} (hn : 0 < n)
    (A : MeasurableFinitePartition (volume : Measure I) r) (phi : I → I)
    (hphi : MeasurePreserving phi volume volume) :
    (∀ (i : Fin n) a, 0 ≤ lebesgueAlignmentWeight A phi i a) ∧
      (∀ i : Fin n, ∑ a, lebesgueAlignmentWeight A phi i a = 1) ∧
      (∀ a, (∑ i : Fin n, lebesgueAlignmentWeight A phi i a)/(n : ℝ) = volume.real (A.cell a)) :=
  aligned_partition_weights_stochastic_and_means hn (lebesgueGridPartition n hn) A
    (lebesgueGridCell_mass hn) phi hphi

end LatinonEntropy

#print axioms LatinonEntropy.lebesgueGridCell_measurable
#print axioms LatinonEntropy.lebesgueGridCell_mass
#print axioms LatinonEntropy.lebesgueGridCell_disjoint
#print axioms LatinonEntropy.lebesgueGridCell_cover_positive
#print axioms LatinonEntropy.lebesgueGridCell_cover_ae
#print axioms LatinonEntropy.lebesgueGridPartition
#print axioms LatinonEntropy.lebesgue_alignment_weights_stochastic_and_means
