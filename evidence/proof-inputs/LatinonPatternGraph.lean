module

public import KernelGraphAEBounds
public import LatinonPatternSampling
public import LatinonKernelFamily

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

abbrev PatternVertex (k l : ℕ) := Fin k ⊕ Fin l

abbrev patternGraphEdge {k l : ℕ} (e : PatternVertex k l × PatternVertex k l) : Prop :=
  match e.1,e.2 with
  | .inl i,.inl j => i < j
  | .inr i,.inr j => i < j
  | .inl _,.inr _ => True
  | .inr _,.inl _ => False

def patternGraphEdges (k l : ℕ) : Finset (PatternVertex k l × PatternVertex k l) :=
  Finset.univ.filter patternGraphEdge

theorem patternGraphEdges_noOpposite (k l : ℕ) : NoOppositeEdges (patternGraphEdges k l) := by
  rintro ⟨u,v⟩ he hs
  simp only [patternGraphEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he hs
  cases u <;> cases v <;> simp_all [patternGraphEdge,Prod.swap] <;> omega

def patternEdgeKernel {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ)
    (e : PatternVertex k l × PatternVertex k l) : I × I → ℝ :=
  match e.1,e.2 with
  | .inl _,.inl _ => A
  | .inr _,.inr _ => B
  | .inl i,.inr j => K (i,j)
  | .inr _,.inl _ => fun _ => 1

def strictPairProduct {n : ℕ} (A : I × I → ℝ) (x : Fin n → I) : ℝ :=
  ∏ i, ∏ j, if i < j then A (x i,x j) else 1

theorem patternGraphProduct_factor {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ) (x : PatternVertex k l → I) :
    kernelGraphProduct (patternGraphEdges k l) (patternEdgeKernel A B K) x=
      strictPairProduct A (x ∘ Sum.inl)*strictPairProduct B (x ∘ Sum.inr)*
        ∏ a : Fin k × Fin l, K a (x (.inl a.1),x (.inr a.2)) := by
  unfold kernelGraphProduct patternGraphEdges strictPairProduct
  rw [Finset.prod_filter,Fintype.prod_prod_type,Fintype.prod_sum_type]
  simp only [Fintype.prod_sum_type,patternGraphEdge,patternEdgeKernel,
    Finset.prod_mul_distrib,Fintype.prod_prod_type,Function.comp_apply]
  simp only [ite_true,ite_false,Finset.prod_const_one,one_mul]
  ring

theorem patternEdgeKernel_measurable {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hK : ∀ a, Measurable (K a)) (e : PatternVertex k l × PatternVertex k l) :
    Measurable (patternEdgeKernel A B K e) := by
  obtain ⟨u,v⟩ := e
  cases u <;> cases v
  · exact hA
  · exact hK _
  · exact measurable_const
  · exact hB

theorem patternEdgeKernel_bounds {k l : ℕ} (A B : I × I → ℝ)
    (K : (Fin k × Fin l) → I × I → ℝ)
    (hA : ∀ᵐ p ∂unitSquareVolume, A p ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ᵐ p ∂unitSquareVolume, B p ∈ Set.Icc (0 : ℝ) 1)
    (hK : ∀ a, ∀ᵐ p ∂unitSquareVolume, K a p ∈ Set.Icc (0 : ℝ) 1)
    (e : PatternVertex k l × PatternVertex k l) :
    ∀ᵐ p ∂unitSquareVolume, patternEdgeKernel A B K e p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨u,v⟩ := e
  cases u <;> cases v
  · exact hA
  · exact hK _
  · exact ae_of_all _ (fun _ => ⟨zero_le_one,le_refl 1⟩)
  · exact hB

theorem strictPairProduct_order (W : LatinonMeasure) {n : ℕ} (x : Fin n → I) :
    strictPairProduct (latinonOrderKernel W) x=
      if StrictMono (W.order ∘ x) then (1 : ℝ) else 0 := by
  unfold strictPairProduct
  by_cases h : StrictMono (W.order ∘ x)
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j _
    by_cases hij : i < j
    · rw [ite_eq_left hij]
      have hm : (x i,x j) ∈ orderRelation W.order := h hij
      exact Set.indicator_of_mem hm _
    · exact ite_eq_right hij
  · rw [ite_eq_right h]
    simp only [StrictMono,Function.comp_apply,not_forall] at h
    obtain ⟨i,j,hij,hn⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [ite_eq_left hij]
    have hm : (x i,x j) ∉ orderRelation W.order := hn
    exact Set.indicator_of_notMem hm _

def patternConfigVertices {k l : ℕ} (c : LatinonPatternConfig k l) : PatternVertex k l → I :=
  Sum.elim c.1 c.2

theorem patternConfigVertices_preserving (k l : ℕ) :
    MeasurePreserving (patternConfigVertices (k := k) (l := l))
      (latinonPatternConfigLaw k l) (vertexSampleLaw (PatternVertex k l)) :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ : PatternVertex k l => (volume : Measure I))

end LatinonEntropy

#print axioms LatinonEntropy.patternGraphEdges_noOpposite
#print axioms LatinonEntropy.patternGraphProduct_factor
#print axioms LatinonEntropy.patternEdgeKernel_measurable
#print axioms LatinonEntropy.patternEdgeKernel_bounds
#print axioms LatinonEntropy.strictPairProduct_order
#print axioms LatinonEntropy.patternConfigVertices_preserving
