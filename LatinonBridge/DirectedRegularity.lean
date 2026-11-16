module

public import LatinonBridge.Regularity
public import LatinonBridge.BlockIntegrals

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval

def taggedBlock (b t : Bool) (p : I × I) : BipartiteSpace × BipartiteSpace :=
  ((b,p.1),(t,p.2))

theorem taggedBlock_measurable (b t : Bool) : Measurable (taggedBlock b t) :=
  (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)

theorem ae_bipartite_block {P : BipartiteSpace × BipartiteSpace → Prop}
    (h : ∀ᵐ p ∂(bipartiteVolume.prod bipartiteVolume), P p) (b t : Bool)
    (hm : MeasurableSet {p : I × I | P (taggedBlock b t p)}) :
    ∀ᵐ p ∂((volume : Measure I).prod volume), P (taggedBlock b t p) := by
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  have hfirst := ae_bipartite_tag (Measure.ae_ae_of_ae_prod h) b
  filter_upwards [hfirst] with x hx
  exact ae_bipartite_tag hx t

def directedStepApprox (P : MeasurablePartition BipartiteSpace bipartiteVolume)
    (W : Graphon BipartiteSpace bipartiteVolume) (p : I × I) : ℝ :=
  Graphon.stepifyFun P W (taggedBlock false true p)

theorem directedStepApprox_measurable
    (P : MeasurablePartition BipartiteSpace bipartiteVolume)
    (W : Graphon BipartiteSpace bipartiteVolume) : Measurable (directedStepApprox P W) :=
  (Graphon.stepifyFun_measurable P W).comp (taggedBlock_measurable false true)

theorem directedStepApprox_bounds
    (P : MeasurablePartition BipartiteSpace bipartiteVolume)
    (W : Graphon BipartiteSpace bipartiteVolume) :
    ∀ᵐ p ∂((volume : Measure I).prod volume), directedStepApprox P W p ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_bipartite_block (Graphon.stepifyFun_mem_Icc_ae P W) false true
  exact measurableSet_Icc.preimage (directedStepApprox_measurable P W)

/-- Directed weak regularity with an actual finite tagged partition and the
correct factor 4. The input may be nonsymmetric and is bounded only a.e. -/
theorem exists_directed_regular_approximation (g : I × I → ℝ) (hg : Measurable g)
    (hb : ∀ᵐ p ∂((volume : Measure I).prod volume), g p ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ P : MeasurablePartition BipartiteSpace bipartiteVolume,
      P.parts.card ≤ Graphon.regularityBound eps ∧
      ∀ (S T : Set I), MeasurableSet S → MeasurableSet T →
        |∫ p in S ×ˢ T, (g p-directedStepApprox P (bipartiteGraphon g hg hb) p)
          ∂((volume : Measure I).prod volume)| ≤ 4*eps := by
  let W := bipartiteGraphon g hg hb
  obtain ⟨P,hcard,hcut⟩ := exists_bipartite_regular_partition g hg hb eps heps
  refine ⟨P,hcard,?_⟩
  intro S T hS hT
  have hstep := Graphon.stepifyFun_mem_Icc_ae P W
  have hglo := bipartiteValue_bounds g hb
  have hfi : Integrable (fun p => bipartiteValue g p-Graphon.stepifyFun P W p)
      (bipartiteVolume.prod bipartiteVolume) := by
    apply Integrable.of_mem_Icc (-1) 1
      ((bipartiteValue_measurable g hg).sub (Graphon.stepifyFun_measurable P W)).aemeasurable
    filter_upwards [hstep,hglo] with p hp hq
    change (-1 : ℝ) ≤ bipartiteValue g p-Graphon.stepifyFun P W p ∧
      bipartiteValue g p-Graphon.stepifyFun P W p ≤ 1
    constructor <;> linarith only [hp.1,hp.2,hq.1,hq.2]
  have hgi : Integrable g ((volume : Measure I).prod volume) :=
    Integrable.of_mem_Icc 0 1 hg.aemeasurable hb
  have hsi : Integrable (directedStepApprox P W) ((volume : Measure I).prod volume) :=
    Integrable.of_mem_Icc 0 1 (directedStepApprox_measurable P W).aemeasurable
      (directedStepApprox_bounds P W)
  have hblock := bipartite_blockIntegral _ hfi false true S T hS (hgi.sub hsi)
  have hgeq : ∀ᵐ p ∂(bipartiteVolume.prod bipartiteVolume),
      W.toAEEqFun p=bipartiteValue g p :=
    AEEqFun.coeFn_mk (μ := bipartiteVolume.prod bipartiteVolume)
      (bipartiteValue g) (bipartiteValue_measurable g hg).aestronglyMeasurable
  have he : Graphon.rectIntegralDiff W (Graphon.stepify P W) ({false} ×ˢ S) ({true} ×ˢ T) =
      ∫ p in (({false} ×ˢ S) ×ˢ ({true} ×ˢ T)),
        (bipartiteValue g p-Graphon.stepifyFun P W p) ∂(bipartiteVolume.prod bipartiteVolume) := by
    apply setIntegral_congr_ae (((measurableSet_singleton false).prod hS).prod
      ((measurableSet_singleton true).prod hT))
    filter_upwards [hgeq,Graphon.stepify_ae P W] with p hp hq _
    rw [hp,hq]
  have htest := (Graphon.abs_rectIntegralDiff_le W (Graphon.stepify P W)
    ((measurableSet_singleton false).prod hS) ((measurableSet_singleton true).prod hT)).trans hcut
  rw [he,hblock,abs_mul] at htest
  norm_num only [abs_of_pos (show (0 : ℝ) < 1/4 by norm_num)] at htest
  change (1/4 : ℝ)*|∫ p in S ×ˢ T, (g p-directedStepApprox P W p)
    ∂((volume : Measure I).prod volume)| ≤ eps at htest
  linarith only [htest]

end LatinonEntropy

#print axioms LatinonEntropy.taggedBlock_measurable
#print axioms LatinonEntropy.ae_bipartite_block
#print axioms LatinonEntropy.directedStepApprox_measurable
#print axioms LatinonEntropy.directedStepApprox_bounds
#print axioms LatinonEntropy.exists_directed_regular_approximation
