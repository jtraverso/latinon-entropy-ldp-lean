module

public import LatinonBridge.BipartiteKernel
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory
open scoped Classical unitInterval NNReal ENNReal

theorem binaryTagMeasure_singleton (b : Bool) : binaryTagMeasure {b}=(1/2 : ℝ≥0∞) := by
  cases b <;> norm_num [binaryTagMeasure,Measure.coe_nnreal_smul_apply]

theorem binaryTagMeasure_real_singleton (b : Bool) : binaryTagMeasure.real {b}=(1/2 : ℝ) := by
  simp only [measureReal_def,binaryTagMeasure_singleton,ENNReal.toReal_div,
    ENNReal.toReal_one,ENNReal.toReal_ofNat]

theorem ae_bipartite_tag {P : BipartiteSpace → Prop}
    (h : ∀ᵐ p ∂bipartiteVolume, P p) (b : Bool) : ∀ᵐ u ∂(volume : Measure I), P (b,u) := by
  have hfirst : ∀ᵐ b ∂binaryTagMeasure, ∀ᵐ u ∂(volume : Measure I), P (b,u) :=
    Measure.ae_ae_of_ae_prod h
  apply ae_iff_of_countable.mp hfirst b
  rw [binaryTagMeasure_singleton]
  norm_num

theorem bipartite_setIntegral (f : BipartiteSpace → ℝ) (hf : Integrable f bipartiteVolume)
    (b : Bool) (S : Set I) :
    (∫ p in ({b} ×ˢ S), f p ∂bipartiteVolume) =
      (1/2 : ℝ)*(∫ u in S, f (b,u)) := by
  rw [setIntegral_prod f hf.integrableOn,integral_singleton,
    binaryTagMeasure_real_singleton,smul_eq_mul]

/-- Exact mass 1/4 of a tagged bipartite rectangle. This is the factor used
to transfer the graphon cut bound back to the original directed kernel. -/
theorem bipartite_blockIntegral (f : BipartiteSpace × BipartiteSpace → ℝ)
    (hf : Integrable f (bipartiteVolume.prod bipartiteVolume))
    (b t : Bool) (S T : Set I) (hS : MeasurableSet S)
    (hblock : Integrable (fun p : I × I => f ((b,p.1),(t,p.2))) (volume.prod volume)) :
    (∫ p in (({b} ×ˢ S) ×ˢ ({t} ×ˢ T)), f p ∂(bipartiteVolume.prod bipartiteVolume)) =
      (1/4 : ℝ)*(∫ p in (S ×ˢ T), f ((b,p.1),(t,p.2)) ∂(volume.prod volume)) := by
  have hfR : Integrable f (bipartiteVolume.prod (bipartiteVolume.restrict ({t} ×ˢ T))) := by
    have h := (hf.integrableOn : IntegrableOn f (Set.univ ×ˢ ({t} ×ˢ T))
      (bipartiteVolume.prod bipartiteVolume))
    simpa only [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ] using h
  have hsection := ae_bipartite_tag hf.prod_right_ae b
  rw [setIntegral_prod f hf.integrableOn,
    bipartite_setIntegral _ hfR.integral_prod_left b S]
  calc
    (1/2 : ℝ)*(∫ u in S, ∫ q in ({t} ×ˢ T), f ((b,u),q) ∂bipartiteVolume)
        = (1/2 : ℝ)*(∫ u in S, (1/2 : ℝ)*(∫ v in T, f ((b,u),(t,v)))) := by
          congr 1
          apply setIntegral_congr_ae hS
          filter_upwards [hsection] with u hu _
          exact bipartite_setIntegral _ hu t T
    _ = (1/4 : ℝ)*(∫ u in S, ∫ v in T, f ((b,u),(t,v))) := by
      rw [integral_const_mul]
      ring
    _ = _ := by rw [setIntegral_prod _ hblock.integrableOn]

end LatinonEntropy

#print axioms LatinonEntropy.binaryTagMeasure_singleton
#print axioms LatinonEntropy.binaryTagMeasure_real_singleton
#print axioms LatinonEntropy.ae_bipartite_tag
#print axioms LatinonEntropy.bipartite_setIntegral
#print axioms LatinonEntropy.bipartite_blockIntegral
