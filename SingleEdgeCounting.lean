module

public import CoordinateResampling
public import EdgeProductFactorization
public import SignedWeightedCut

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

def kernelGraphDensity {V : Type*} [Fintype V] (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) : ℝ := ∫ x, kernelGraphProduct E K x ∂vertexSampleLaw V

theorem integrable_kernelGraphProduct {V : Type*} [Fintype V] (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hKm : ∀ e ∈ E, Measurable (K e))
    (hKb : ∀ e ∈ E, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (kernelGraphProduct E K) (vertexSampleLaw V) :=
  Integrable.of_mem_Icc 0 1 (measurable_kernelGraphProduct E K hKm).aemeasurable
    (ae_of_all _ (kernelGraphProduct_mem_Icc E K hKb))

theorem kernelGraphProduct_update_sub {V : Type*} [DecidableEq V] (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (a : V × V) (ha : a ∈ E) (H : I × I → ℝ) (x : V → I) :
    kernelGraphProduct E K x-kernelGraphProduct E (update K a H) x=
      (K a (x a.1,x a.2)-H (x a.1,x a.2))*kernelGraphProduct (E.erase a) K x := by
  have heq : kernelGraphProduct (E.erase a) (update K a H) x=kernelGraphProduct (E.erase a) K x := by
    unfold kernelGraphProduct
    apply Finset.prod_congr rfl
    intro e he
    rw [update_of_ne (Finset.mem_erase.mp he).1]
  have hK := Finset.mul_prod_erase E (fun e => K e (x e.1,x e.2)) ha
  have hH := Finset.mul_prod_erase E (fun e => update K a H e (x e.1,x e.2)) ha
  change K a (x a.1,x a.2)*kernelGraphProduct (E.erase a) K x=kernelGraphProduct E K x at hK
  change update K a H a (x a.1,x a.2)*kernelGraphProduct (E.erase a) (update K a H) x=
    kernelGraphProduct E (update K a H) x at hH
  rw [update_self,heq] at hH
  rw [← hK,← hH]
  ring

/-- Replacing one edge kernel changes the finite product density by at
most its cut error, with constant one. -/
theorem kernelGraphDensity_single_edge {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hE : NoOppositeEdges E)
    (K : (V × V) → I × I → ℝ) (hKm : ∀ e ∈ E, Measurable (K e))
    (hKb : ∀ e ∈ E, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1)
    (a : V × V) (ha : a ∈ E) (H : I × I → ℝ) (hHm : Measurable H)
    (hHb : ∀ p, H p ∈ Set.Icc (0 : ℝ) 1) (eps : ℝ) (hcut : KernelCutClose (K a) H eps) :
    |kernelGraphDensity E K-kernelGraphDensity E (update K a H)| ≤ eps := by
  have hdist : a.1 ≠ a.2 := noOppositeEdges_distinct E hE a ha
  have hUm (e : V × V) (he : e ∈ E) : Measurable (update K a H e) := by
    by_cases hea : e=a
    · subst e
      simpa only [update_self] using hHm
    · simpa only [update_of_ne hea] using hKm e he
  have hUb (e : V × V) (he : e ∈ E) (p : I × I) : update K a H e p ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases hea : e=a
    · subst e
      simpa only [update_self] using hHb p
    · simpa only [update_of_ne hea] using hKb e he p
  have hKi := integrable_kernelGraphProduct E K hKm hKb
  have hUi := integrable_kernelGraphProduct E (update K a H) hUm hUb
  let D : (V → I) → ℝ := fun x => kernelGraphProduct E K x-kernelGraphProduct E (update K a H) x
  have hDi : Integrable D (vertexSampleLaw V) := hKi.sub hUi
  have hSm : ∀ e ∈ E.erase a, Measurable (K e) := fun e he => hKm e (Finset.mem_of_mem_erase he)
  have hSb : ∀ e ∈ E.erase a, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1 :=
    fun e he => hKb e (Finset.mem_of_mem_erase he)
  have hinner (r : V → I) :
      |∫ p, D (resamplePair a.1 a.2 (r,p)) ∂unitSquareVolume| ≤ eps := by
    have hpoint (p : I × I) : D (resamplePair a.1 a.2 (r,p))=
        (edgeProductLeft (E.erase a) K a.1 r p.1*edgeProductRight (E.erase a) K a.1 a.2 r p.2)*
          (K a p-H p) := by
      have hselect : ((resamplePair a.1 a.2 (r,p)) a.1,(resamplePair a.1 a.2 (r,p)) a.2)=p := by
        apply Prod.ext
        · simp only [resamplePair,update_of_ne hdist,update_self]
        · simp only [resamplePair,update_self]
      dsimp only [D]
      rw [kernelGraphProduct_update_sub E K a ha H,hselect]
      change (K a p-H p)*kernelGraphProduct (E.erase a) K (update (update r a.1 p.1) a.2 p.2)=_
      rw [kernelGraphProduct_separate (E.erase a) K a.1 a.2 hdist
        (noOppositeEdges_erased_separate E hE a ha)]
      ring
    rw [integral_congr_ae (ae_of_all _ hpoint)]
    exact kernelCutClose_weighted (K a) H (hKm a ha) hHm
      (Integrable.of_mem_Icc 0 1 (hKm a ha).aemeasurable (ae_of_all _ (hKb a ha)))
      (Integrable.of_mem_Icc 0 1 hHm.aemeasurable (ae_of_all _ hHb))
      (edgeProductLeft (E.erase a) K a.1 r) (edgeProductRight (E.erase a) K a.1 a.2 r)
      (measurable_edgeProductLeft _ K hSm _ r) (measurable_edgeProductRight _ K hSm _ _ r)
      (ae_of_all _ (edgeProductLeft_mem_Icc _ K hSb _ r))
      (ae_of_all _ (edgeProductRight_mem_Icc _ K hSb _ _ r)) eps hcut
  have hres := integral_resamplePair a.1 a.2 D hDi
  have houter : Integrable (fun r => ∫ p, D (resamplePair a.1 a.2 (r,p)) ∂unitSquareVolume)
      (vertexSampleLaw V) :=
    ((resamplePair_preserving a.1 a.2).integrable_comp_of_integrable hDi).integral_prod_left
  unfold kernelGraphDensity
  rw [← integral_sub hKi hUi]
  change |∫ x, D x ∂vertexSampleLaw V| ≤ eps
  rw [hres]
  calc
    _ ≤ ∫ r, |∫ p, D (resamplePair a.1 a.2 (r,p)) ∂unitSquareVolume| ∂vertexSampleLaw V :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _r : V → I, eps ∂vertexSampleLaw V :=
      integral_mono_ae houter.abs (integrable_const eps) (ae_of_all _ hinner)
    _ = eps := by simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

end LatinonEntropy

#print axioms LatinonEntropy.integrable_kernelGraphProduct
#print axioms LatinonEntropy.kernelGraphProduct_update_sub
#print axioms LatinonEntropy.kernelGraphDensity_single_edge
