module

public import LatinonBridge.FiniteTestPartition
public import LatinonBridge.DirectedRegularity

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Finset
open scoped Classical unitInterval

abbrev TaggedPartitionTest {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume) :=
  Σ j : Fin k, {S // S ∈ (P j).parts} × Bool

def taggedFamilyTests {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (i : TaggedPartitionTest P) : Set I := {u | (i.2.2,u) ∈ i.2.1.1}

theorem taggedFamilyTests_measurable {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume) (i : TaggedPartitionTest P) :
    MeasurableSet (taggedFamilyTests P i) :=
  ((P i.1).measurable_parts _ i.2.1.2).preimage (measurable_const.prodMk measurable_id)

def commonDirectedPartition {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume) :
    MeasurablePartition I volume :=
  finiteTestPartition (taggedFamilyTests P) (taggedFamilyTests_measurable P)

theorem commonDirectedPartition_card {k B : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (hP : ∀ j, (P j).parts.card ≤ B) :
    (commonDirectedPartition P).parts.card ≤ 2^(2*k*B) := by
  have hcard : Fintype.card (TaggedPartitionTest P) ≤ 2*k*B := by
    simp only [TaggedPartitionTest,Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,
      Fintype.card_coe]
    calc
      (∑ j : Fin k, (P j).parts.card*2) ≤ ∑ _j : Fin k, B*2 :=
        Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right 2 (hP j))
      _ = 2*k*B := by simp [mul_comm,mul_left_comm]
  exact (finiteTestPartition_card (taggedFamilyTests P) (taggedFamilyTests_measurable P)).trans
    (Nat.pow_le_pow_right (by omega) hcard)

theorem commonDirectedPartition_decides {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (A : Set I) (hA : A ∈ (commonDirectedPartition P).parts)
    (j : Fin k) (S : Set BipartiteSpace) (hS : S ∈ (P j).parts) (b : Bool) :
    A ⊆ {u | (b,u) ∈ S} ∨ A ⊆ {u | (b,u) ∈ S}ᶜ :=
  finiteTestPartition_decides (taggedFamilyTests P) (taggedFamilyTests_measurable P)
    A hA ⟨j,⟨⟨S,hS⟩,b⟩⟩

/-- All restricted step approximants are exactly constant on the SAME
finite partition, with one common row/column coordinate system. -/
theorem directedStepApprox_constant_on_common_parts {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (j : Fin k) (W : Graphon BipartiteSpace bipartiteVolume)
    (A B : Set I) (hA : A ∈ (commonDirectedPartition P).parts)
    (hB : B ∈ (commonDirectedPartition P).parts)
    (x x' y y' : I) (hx : x ∈ A) (hx' : x' ∈ A) (hy : y ∈ B) (hy' : y' ∈ B) :
    directedStepApprox (P j) W (x,y)=directedStepApprox (P j) W (x',y') := by
  have hrow (S : Set BipartiteSpace) (hS : S ∈ (P j).parts) :
      (false,x) ∈ S ↔ (false,x') ∈ S := by
    rcases commonDirectedPartition_decides P A hA j S hS false with h | h
    · exact ⟨fun _ => h hx',fun _ => h hx⟩
    · exact iff_of_false (h hx) (h hx')
  have hcol (T : Set BipartiteSpace) (hT : T ∈ (P j).parts) :
      (true,y) ∈ T ↔ (true,y') ∈ T := by
    rcases commonDirectedPartition_decides P B hB j T hT true with h | h
    · exact ⟨fun _ => h hy',fun _ => h hy⟩
    · exact iff_of_false (h hy) (h hy')
  unfold directedStepApprox Graphon.stepifyFun
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Set.indicator_apply,Set.mem_prod,taggedBlock,hrow S hS,hcol T hT]

/-- Stepification is bounded at every point,including points outside its
almost-everywhere partition cover,where the defining finite sums vanish. -/
theorem stepifyFun_bounds_everywhere
    (P : MeasurablePartition BipartiteSpace bipartiteVolume)
    (W : Graphon BipartiteSpace bipartiteVolume) (p : BipartiteSpace × BipartiteSpace) :
    Graphon.stepifyFun P W p ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hr : ∃ S ∈ P.parts, p.1 ∈ S
  · obtain ⟨S,hS,hx⟩ := hr
    by_cases hc : ∃ T ∈ P.parts, p.2 ∈ T
    · obtain ⟨T,hT,hy⟩ := hc
      rw [Graphon.stepifyFun_eq_rectAverage P W hS hT ⟨hx,hy⟩]
      exact Graphon.rectAverage_mem_Icc W S T (P.measurable_parts S hS) (P.measurable_parts T hT)
    · have he : Graphon.stepifyFun P W p=0 := by
        unfold Graphon.stepifyFun
        apply Finset.sum_eq_zero
        intro S' _
        apply Finset.sum_eq_zero
        intro T hT
        exact Set.indicator_of_notMem (fun hp => hc ⟨T,hT,hp.2⟩) _
      rw [he]
      exact ⟨le_rfl,zero_le_one⟩
  · have he : Graphon.stepifyFun P W p=0 := by
      unfold Graphon.stepifyFun
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T _
      exact Set.indicator_of_notMem (fun hp => hr ⟨S,hS,hp.1⟩) _
    rw [he]
    exact ⟨le_rfl,zero_le_one⟩

theorem directedStepApprox_bounds_everywhere
    (P : MeasurablePartition BipartiteSpace bipartiteVolume)
    (W : Graphon BipartiteSpace bipartiteVolume) (p : I × I) :
    directedStepApprox P W p ∈ Set.Icc (0 : ℝ) 1 :=
  stepifyFun_bounds_everywhere P W (taggedBlock false true p)

def commonDirectedCoefficient {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (j : Fin k) (W : Graphon BipartiteSpace bipartiteVolume) (A B : Set I) : ℝ :=
  if h : A.Nonempty ∧ B.Nonempty then
    directedStepApprox (P j) W (h.1.choose,h.2.choose) else 0

theorem commonDirectedCoefficient_bounds {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (j : Fin k) (W : Graphon BipartiteSpace bipartiteVolume) (A B : Set I) :
    commonDirectedCoefficient P j W A B ∈ Set.Icc (0 : ℝ) 1 := by
  unfold commonDirectedCoefficient
  split_ifs
  · exact directedStepApprox_bounds_everywhere _ _ _
  · exact ⟨le_rfl,zero_le_one⟩

theorem directedStepApprox_eq_commonCoefficient {k : ℕ}
    (P : Fin k → MeasurablePartition BipartiteSpace bipartiteVolume)
    (j : Fin k) (W : Graphon BipartiteSpace bipartiteVolume)
    (A B : Set I) (hA : A ∈ (commonDirectedPartition P).parts)
    (hB : B ∈ (commonDirectedPartition P).parts)
    (x y : I) (hx : x ∈ A) (hy : y ∈ B) :
    directedStepApprox (P j) W (x,y)=commonDirectedCoefficient P j W A B := by
  have hne : A.Nonempty ∧ B.Nonempty := ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  unfold commonDirectedCoefficient
  rw [dite_eq_left hne]
  exact directedStepApprox_constant_on_common_parts P j W A B hA hB x hne.1.choose y hne.2.choose
    hx hne.1.choose_spec hy hne.2.choose_spec

/-- Uniform simultaneous weak regularity for a finite family of DIRECTED
kernels. All approximants use one common partition with a uniform bound. -/
theorem exists_simultaneous_directed_regular_approximation {k : ℕ}
    (g : Fin k → I × I → ℝ) (hg : ∀ j, Measurable (g j))
    (hb : ∀ j, ∀ᵐ p ∂((volume : Measure I).prod volume), g j p ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ Q : MeasurablePartition I volume,
    ∃ a : Fin k → Set I → Set I → ℝ,
    ∃ h : Fin k → I × I → ℝ,
      Q.parts.card ≤ 2^(2*k*Graphon.regularityBound eps) ∧
      (∀ j A B, a j A B ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ j, Measurable (h j) ∧ (∀ p, h j p ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ A ∈ Q.parts, ∀ B ∈ Q.parts, ∀ x ∈ A, ∀ y ∈ B, h j (x,y)=a j A B) ∧
        ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
          |∫ p in S ×ˢ T, (g j p-h j p) ∂((volume : Measure I).prod volume)| ≤ 4*eps := by
  choose P hcard hclose using
    (fun j => exists_directed_regular_approximation (g j) (hg j) (hb j) eps heps)
  let W (j : Fin k) := bipartiteGraphon (g j) (hg j) (hb j)
  refine ⟨commonDirectedPartition P,fun j => commonDirectedCoefficient P j (W j),
    fun j => directedStepApprox (P j) (W j),commonDirectedPartition_card P hcard,?_,?_⟩
  · exact fun j A B => commonDirectedCoefficient_bounds P j (W j) A B
  · intro j
    refine ⟨directedStepApprox_measurable _ _,directedStepApprox_bounds_everywhere _ _,?_,hclose j⟩
    intro A hA B hB x hx y hy
    exact directedStepApprox_eq_commonCoefficient P j (W j) A B hA hB x y hx hy

end LatinonEntropy

#print axioms LatinonEntropy.taggedFamilyTests_measurable
#print axioms LatinonEntropy.commonDirectedPartition
#print axioms LatinonEntropy.commonDirectedPartition_card
#print axioms LatinonEntropy.commonDirectedPartition_decides
#print axioms LatinonEntropy.directedStepApprox_constant_on_common_parts
#print axioms LatinonEntropy.stepifyFun_bounds_everywhere
#print axioms LatinonEntropy.directedStepApprox_bounds_everywhere
#print axioms LatinonEntropy.commonDirectedCoefficient_bounds
#print axioms LatinonEntropy.directedStepApprox_eq_commonCoefficient
#print axioms LatinonEntropy.exists_simultaneous_directed_regular_approximation
