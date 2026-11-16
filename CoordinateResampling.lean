module

public import Mathlib
public import LatinonSymbolCompression

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

def vertexSampleLaw (V : Type*) [Fintype V] : Measure (V → I) :=
  Measure.pi (fun _ => (volume : Measure I))

instance vertexSampleLaw_probability (V : Type*) [Fintype V] :
    IsProbabilityMeasure (vertexSampleLaw V) := by
  unfold vertexSampleLaw
  infer_instance

theorem prod_update_one_mul {V M : Type*} [Fintype V] [DecidableEq V] [CommMonoid M]
    (a : V → M) (u : V) : (∏ w, update a u 1 w)*a u=∏ w, a w := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ u),one_mul,Finset.sdiff_singleton_eq_erase]
  exact Finset.prod_erase_mul Finset.univ a (Finset.mem_univ u)

def resampleCoordinate {V : Type*} [DecidableEq V] (u : V) (p : (V → I) × I) : V → I :=
  update p.1 u p.2

theorem measurable_resampleCoordinate {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    Measurable (resampleCoordinate u) := by
  exact measurable_update'

theorem resampleCoordinate_preimage_box {V : Type*} [Fintype V] [DecidableEq V]
    (u : V) (S : V → Set I) :
    resampleCoordinate u ⁻¹' Set.pi Set.univ S=
      Set.pi Set.univ (update S u Set.univ) ×ˢ S u := by
  ext p
  simp only [Set.mem_preimage,Set.mem_univ_pi,Set.mem_prod,resampleCoordinate]
  constructor
  · intro hp
    constructor
    · intro w
      by_cases hw : w=u
      · subst w
        simp only [update_self,Set.mem_univ]
      · simpa only [update_of_ne hw] using hp w
    · simpa only [update_self] using hp u
  · rintro ⟨hp,hu⟩ w
    by_cases hw : w=u
    · subst w
      simpa only [update_self] using hu
    · simpa only [update_of_ne hw] using hp w

/-- Replacing one coordinate by a fresh uniform preserves the full product law. -/
theorem resampleCoordinate_preserving {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    MeasurePreserving (resampleCoordinate u)
      ((vertexSampleLaw V).prod (volume : Measure I)) (vertexSampleLaw V) := by
  refine ⟨measurable_resampleCoordinate u,?_⟩
  symm
  apply Measure.pi_eq
  intro S hS
  rw [Measure.map_apply (measurable_resampleCoordinate u) (MeasurableSet.univ_pi hS),
    resampleCoordinate_preimage_box,Measure.prod_prod,vertexSampleLaw,Measure.pi_pi]
  have hfun : (fun w => (volume : Measure I) (update S u Set.univ w))=
      update (fun w => (volume : Measure I) (S w)) u 1 := by
    funext w
    simpa only [measure_univ] using
      (Function.apply_update (fun _ : V => (volume : Measure I)) S u Set.univ w)
  rw [hfun]
  exact prod_update_one_mul (fun w => (volume : Measure I) (S w)) u

def resamplePair {V : Type*} [DecidableEq V] (u v : V) (p : (V → I) × (I × I)) : V → I :=
  update (update p.1 u p.2.1) v p.2.2

theorem resamplePair_preserving {V : Type*} [Fintype V] [DecidableEq V] (u v : V) :
    MeasurePreserving (resamplePair u v) ((vertexSampleLaw V).prod unitSquareVolume) (vertexSampleLaw V) := by
  have hA := (measurePreserving_prodAssoc (vertexSampleLaw V) (volume : Measure I) (volume : Measure I)).symm
  have hU := (resampleCoordinate_preserving u).prod (MeasurePreserving.id (volume : Measure I))
  exact (resampleCoordinate_preserving v).comp (hU.comp hA)

theorem integral_resamplePair {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (f : (V → I) → ℝ) (hf : Integrable f (vertexSampleLaw V)) :
    (∫ x, f x ∂vertexSampleLaw V)=
      ∫ r, ∫ p, f (resamplePair u v (r,p)) ∂unitSquareVolume ∂vertexSampleLaw V := by
  have hm := resamplePair_preserving u v
  have hfmap : AEStronglyMeasurable f
      (Measure.map (resamplePair u v) ((vertexSampleLaw V).prod unitSquareVolume)) := by
    rw [hm.map_eq]
    exact hf.aestronglyMeasurable
  have he := integral_map hm.measurable.aemeasurable hfmap
  rw [hm.map_eq] at he
  exact he.trans (integral_prod _ (hm.integrable_comp_of_integrable hf))

end LatinonEntropy

#print axioms LatinonEntropy.vertexSampleLaw_probability
#print axioms LatinonEntropy.prod_update_one_mul
#print axioms LatinonEntropy.measurable_resampleCoordinate
#print axioms LatinonEntropy.resampleCoordinate_preimage_box
#print axioms LatinonEntropy.resampleCoordinate_preserving
#print axioms LatinonEntropy.resamplePair_preserving
#print axioms LatinonEntropy.integral_resamplePair
