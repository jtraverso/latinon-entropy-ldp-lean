module

public import FiniteKernelCounting

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory Function
open scoped Classical unitInterval

theorem vertexPair_preserving {V : Type*} [Fintype V] (u v : V) (huv : u ≠ v) :
    MeasurePreserving (fun x : V → I => (x u,x v)) (vertexSampleLaw V) unitSquareVolume := by
  have hi := (measurable_pi_apply u : Measurable (fun x : V → I => x u))
  have hj := (measurable_pi_apply v : Measurable (fun x : V → I => x v))
  have hind := (iIndepFun_pi (μ := fun _ : V => (volume : Measure I))
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun huv
  have hmap := hind.map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable
  rw [(measurePreserving_eval (fun _ : V => (volume : Measure I)) u).map_eq,
    (measurePreserving_eval (fun _ : V => (volume : Measure I)) v).map_eq] at hmap
  exact ⟨hi.prodMk hj,hmap⟩

def clipUnitKernel (K : I × I → ℝ) (p : I × I) : ℝ := max 0 (min 1 (K p))

theorem measurable_clipUnitKernel (K : I × I → ℝ) (hK : Measurable K) :
    Measurable (clipUnitKernel K) := measurable_const.max (measurable_const.min hK)

theorem clipUnitKernel_mem_Icc (K : I × I → ℝ) (p : I × I) :
    clipUnitKernel K p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem clipUnitKernel_ae_eq (K : I × I → ℝ)
    (hK : ∀ᵐ p ∂unitSquareVolume, K p ∈ Set.Icc (0 : ℝ) 1) :
    clipUnitKernel K=ᵐ[unitSquareVolume] K := by
  filter_upwards [hK] with p hp
  exact (congrArg (max (0 : ℝ)) (min_eq_right hp.2)).trans (max_eq_right hp.1)

theorem kernelCutClose_clipUnitKernel (K H : I × I → ℝ)
    (hK : ∀ᵐ p ∂unitSquareVolume, K p ∈ Set.Icc (0 : ℝ) 1)
    (hH : ∀ᵐ p ∂unitSquareVolume, H p ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (hcut : KernelCutClose K H eps) :
    KernelCutClose (clipUnitKernel K) (clipUnitKernel H) eps := by
  intro S T hS hT
  calc
    _ = |∫ p in S ×ˢ T, K p-H p ∂unitSquareVolume| :=
      congrArg abs (integral_congr_ae (ae_restrict_of_ae
        ((clipUnitKernel_ae_eq K hK).sub (clipUnitKernel_ae_eq H hH))))
    _ ≤ eps := hcut S T hS hT

theorem kernelGraphProduct_clip_ae {V : Type*} [Fintype V] (E : Finset (V × V))
    (hE : NoOppositeEdges E) (K : (V × V) → I × I → ℝ)
    (hK : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, K e p ∈ Set.Icc (0 : ℝ) 1) :
    kernelGraphProduct E (fun e => clipUnitKernel (K e))=ᵐ[vertexSampleLaw V] kernelGraphProduct E K := by
  have hall : ∀ᵐ x ∂vertexSampleLaw V, ∀ e ∈ E,
      clipUnitKernel (K e) (x e.1,x e.2)=K e (x e.1,x e.2) := by
    simp only [ae_all_iff]
    intro e he
    exact (vertexPair_preserving e.1 e.2 (noOppositeEdges_distinct E hE e he)).quasiMeasurePreserving.ae
      (clipUnitKernel_ae_eq (K e) (hK e he))
  filter_upwards [hall] with x hx
  unfold kernelGraphProduct
  exact Finset.prod_congr rfl (fun e he => hx e he)

theorem kernelGraphDensity_clip {V : Type*} [Fintype V] (E : Finset (V × V))
    (hE : NoOppositeEdges E) (K : (V × V) → I × I → ℝ)
    (hK : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, K e p ∈ Set.Icc (0 : ℝ) 1) :
    kernelGraphDensity E (fun e => clipUnitKernel (K e))=kernelGraphDensity E K :=
  integral_congr_ae (kernelGraphProduct_clip_ae E hE K hK)

theorem integrable_kernelGraphProduct_ae {V : Type*} [Fintype V] (E : Finset (V × V))
    (hE : NoOppositeEdges E) (K : (V × V) → I × I → ℝ)
    (hKm : ∀ e ∈ E, Measurable (K e))
    (hKb : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, K e p ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (kernelGraphProduct E K) (vertexSampleLaw V) :=
  (integrable_kernelGraphProduct E (fun e => clipUnitKernel (K e))
    (fun e he => measurable_clipUnitKernel (K e) (hKm e he))
    (fun e _ => clipUnitKernel_mem_Icc (K e))).congr (kernelGraphProduct_clip_ae E hE K hKb)

/-- The colored counting lemma with the a.e. bounds actually supplied by
Latinon symbol compressions. There is no pointwise-boundedness hypothesis. -/
theorem kernelGraphDensity_counting_ae {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (hE : NoOppositeEdges E)
    (K H : (V × V) → I × I → ℝ)
    (hKm : ∀ e ∈ E, Measurable (K e)) (hHm : ∀ e ∈ E, Measurable (H e))
    (hKb : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, K e p ∈ Set.Icc (0 : ℝ) 1)
    (hHb : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, H e p ∈ Set.Icc (0 : ℝ) 1)
    (eps : (V × V) → ℝ) (hcut : ∀ e ∈ E, KernelCutClose (K e) (H e) (eps e)) :
    |kernelGraphDensity E K-kernelGraphDensity E H| ≤ ∑ e ∈ E, eps e := by
  have h := kernelGraphDensity_counting E hE (fun e => clipUnitKernel (K e))
    (fun e => clipUnitKernel (H e))
    (fun e he => measurable_clipUnitKernel (K e) (hKm e he))
    (fun e he => measurable_clipUnitKernel (H e) (hHm e he))
    (fun e _ => clipUnitKernel_mem_Icc (K e)) (fun e _ => clipUnitKernel_mem_Icc (H e)) eps
    (fun e he => kernelCutClose_clipUnitKernel (K e) (H e) (hKb e he) (hHb e he) (eps e) (hcut e he))
  rw [kernelGraphDensity_clip E hE K hKb,kernelGraphDensity_clip E hE H hHb] at h
  exact h

/-- Independent MP changes at every vertex preserve the product density.
In particular, row and column vertices may use different relabelings. -/
theorem kernelGraphDensity_nodewise_relabel {V : Type*} [Fintype V]
    (E : Finset (V × V)) (hE : NoOppositeEdges E)
    (K : (V × V) → I × I → ℝ) (hKm : ∀ e ∈ E, Measurable (K e))
    (hKb : ∀ e ∈ E, ∀ᵐ p ∂unitSquareVolume, K e p ∈ Set.Icc (0 : ℝ) 1)
    (f : V → I → I) (hf : ∀ v, MeasurePreserving (f v) volume volume) :
    kernelGraphDensity E (fun e p => K e (f e.1 p.1,f e.2 p.2))=kernelGraphDensity E K := by
  have hm : MeasurePreserving (fun x : V → I => fun v => f v (x v))
      (vertexSampleLaw V) (vertexSampleLaw V) :=
    measurePreserving_pi (fun _ : V => (volume : Measure I))
      (fun _ : V => (volume : Measure I)) hf
  have hi := integrable_kernelGraphProduct_ae E hE K hKm hKb
  have hmap : AEStronglyMeasurable (kernelGraphProduct E K)
      (Measure.map (fun x v => f v (x v)) (vertexSampleLaw V)) := by
    rw [hm.map_eq]
    exact hi.aestronglyMeasurable
  have h := integral_map hm.measurable.aemeasurable hmap
  rw [hm.map_eq] at h
  exact h.symm

end LatinonEntropy

#print axioms LatinonEntropy.vertexPair_preserving
#print axioms LatinonEntropy.measurable_clipUnitKernel
#print axioms LatinonEntropy.clipUnitKernel_mem_Icc
#print axioms LatinonEntropy.clipUnitKernel_ae_eq
#print axioms LatinonEntropy.kernelCutClose_clipUnitKernel
#print axioms LatinonEntropy.kernelGraphProduct_clip_ae
#print axioms LatinonEntropy.kernelGraphDensity_clip
#print axioms LatinonEntropy.integrable_kernelGraphProduct_ae
#print axioms LatinonEntropy.kernelGraphDensity_counting_ae
#print axioms LatinonEntropy.kernelGraphDensity_nodewise_relabel
