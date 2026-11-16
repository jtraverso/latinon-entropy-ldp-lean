module

public import LatinonPatternSampling
public import LebesgueGridPartition

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def patternBinAssignments {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    Finset ((Fin k × Fin l) → Fin q) :=
  Finset.univ.filter (fun b => ∀ a c, P a < P c → b a < b c)

def patternBinRectangle {k l q : ℕ} (b : (Fin k × Fin l) → Fin q) :
    Set ((Fin k × Fin l) → I) := Set.pi Set.univ (fun a => lebesgueGridCell (b a))

def coarsePatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    Set ((Fin k × Fin l) → I) := ⋃ b ∈ patternBinAssignments P q, patternBinRectangle b

def symbolGridCollision (k l q : ℕ) : Set ((Fin k × Fin l) → I) :=
  {z | ∃ a b, a ≠ b ∧ ∃ j : Fin q, z a ∈ lebesgueGridCell j ∧ z b ∈ lebesgueGridCell j}

theorem measurableSet_patternBinRectangle {k l q : ℕ} (b : (Fin k × Fin l) → Fin q) :
    MeasurableSet (patternBinRectangle b) :=
  MeasurableSet.univ_pi (fun a => lebesgueGridCell_measurable (b a))

theorem measurableSet_coarsePatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) (q : ℕ) :
    MeasurableSet (coarsePatternRealizations P q) :=
  MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ => measurableSet_patternBinRectangle b))

theorem measurableSet_symbolGridCollision (k l q : ℕ) :
    MeasurableSet (symbolGridCollision k l q) := by
  unfold symbolGridCollision
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion (fun a => MeasurableSet.iUnion (fun b => ?_))
  by_cases h : a=b
  · simp only [h,ne_eq,not_true_eq_false,Set.ofPred_false,Set.empty_inter]
    exact MeasurableSet.empty
  · simp only [h,ne_eq,not_false_eq_true,Set.ofPred_true,Set.univ_inter]
    exact MeasurableSet.iUnion (fun j =>
      ((lebesgueGridCell_measurable j).preimage (measurable_pi_apply a)).inter
        ((lebesgueGridCell_measurable j).preimage (measurable_pi_apply b)))

theorem patternBinRectangle_disjoint {k l q : ℕ} (hq : 0 < q)
    (b c : (Fin k × Fin l) → Fin q) (hbc : b ≠ c) :
    Disjoint (patternBinRectangle b) (patternBinRectangle c) := by
  obtain ⟨a,ha⟩ := Function.ne_iff.mp hbc
  apply Set.disjoint_left.mpr
  intro z hb hc
  exact Set.disjoint_left.mp (lebesgueGridCell_disjoint hq (b a) (c a) ha)
    (Set.mem_univ_pi.mp hb a) (Set.mem_univ_pi.mp hc a)

theorem coarsePatternRealizations_subset {k l q : ℕ} (P : LatinOrderPattern k l) (hq : 0 < q) :
    coarsePatternRealizations P q ⊆ unitOrderPatternRealizations P := by
  intro z hz
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hb,hz⟩ := Set.mem_iUnion.mp hb
  have hgood := (Finset.mem_filter.mp hb).2
  intro a c hac
  have hsep := lebesgueGrid_separation hq (hgood a c hac)
  have ha := Set.mem_univ_pi.mp hz a
  have hc := Set.mem_univ_pi.mp hz c
  change symbolGridLower (b a) < (z a : ℝ) ∧ (z a : ℝ) ≤ symbolGridUpper (b a) at ha
  change symbolGridLower (b c) < (z c : ℝ) ∧ (z c : ℝ) ≤ symbolGridUpper (b c) at hc
  exact lt_of_le_of_lt (ha.2.trans hsep) hc.1

theorem mem_coarsePatternRealizations_of_no_collision {k l q : ℕ}
    (P : LatinOrderPattern k l) (hq : 0 < q) (z : (Fin k × Fin l) → I)
    (hz : z ∈ unitOrderPatternRealizations P)
    (hcover : ∀ a, ∃ j : Fin q, z a ∈ lebesgueGridCell j)
    (hcollision : z ∉ symbolGridCollision k l q) : z ∈ coarsePatternRealizations P q := by
  choose b hb using hcover
  have hgood : ∀ a c, P a < P c → b a < b c := by
    intro a c hac
    have hne : a ≠ c := fun he => (ne_of_lt hac) (congrArg P he)
    have hbc : b a ≠ b c := by
      intro he
      exact hcollision ⟨a,c,hne,b a,hb a,by simpa only [he] using hb c⟩
    rcases lt_or_gt_of_ne hbc with hlt|hgt
    · exact hlt
    · have hsep := lebesgueGrid_separation hq hgt
      have ha := hb a
      have hc := hb c
      change symbolGridLower (b a) < (z a : ℝ) ∧ (z a : ℝ) ≤ symbolGridUpper (b a) at ha
      change symbolGridLower (b c) < (z c : ℝ) ∧ (z c : ℝ) ≤ symbolGridUpper (b c) at hc
      have hv := hz a c hac
      exact False.elim ((not_lt_of_ge (hc.2.trans hsep)) (ha.1.trans hv))
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ b,hgood⟩,Set.mem_univ_pi.mpr hb⟩⟩

end LatinonEntropy

#print axioms LatinonEntropy.measurableSet_patternBinRectangle
#print axioms LatinonEntropy.measurableSet_coarsePatternRealizations
#print axioms LatinonEntropy.measurableSet_symbolGridCollision
#print axioms LatinonEntropy.patternBinRectangle_disjoint
#print axioms LatinonEntropy.coarsePatternRealizations_subset
#print axioms LatinonEntropy.mem_coarsePatternRealizations_of_no_collision
