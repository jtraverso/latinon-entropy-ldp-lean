module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

/-- Conditional independent sampling of a finite family of coordinates. -/
def finiteIndependentKernel {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] : Kernel A (∀ j, B j) where
  toFun a := Measure.pi (fun j => K j a)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨S,hS,rfl⟩
    have hSm : ∀ j, MeasurableSet (S j) := fun j => hS j (Set.mem_univ j)
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_fun_prod _ (fun j _ => (K j).measurable_coe (hSm j))

theorem finiteIndependentKernel_apply {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] (a : A) :
    finiteIndependentKernel K a=Measure.pi (fun j => K j a) := rfl

instance finiteIndependentKernel_markov {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] :
    IsMarkovKernel (finiteIndependentKernel K) :=
  ⟨fun a => by rw [finiteIndependentKernel_apply]; infer_instance⟩

theorem finiteIndependentKernel_rectangle {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)] (a : A)
    (S : ∀ j, Set (B j)) :
    finiteIndependentKernel K a (Set.pi Set.univ S)=∏ j, K j a (S j) := by
  rw [finiteIndependentKernel_apply,Measure.pi_pi]

theorem measurable_finiteIndependentKernel_event {A J : Type*} [MeasurableSpace A] [Fintype J]
    {B : J → Type*} [∀ j, MeasurableSpace (B j)]
    (K : ∀ j, Kernel A (B j)) [∀ j, IsMarkovKernel (K j)]
    (S : Set (∀ j, B j)) (hS : MeasurableSet S) :
    Measurable (fun a => finiteIndependentKernel K a S) :=
  (finiteIndependentKernel K).measurable_coe hS

end LatinonEntropy

#print axioms LatinonEntropy.finiteIndependentKernel
#print axioms LatinonEntropy.finiteIndependentKernel_apply
#print axioms LatinonEntropy.finiteIndependentKernel_markov
#print axioms LatinonEntropy.finiteIndependentKernel_rectangle
#print axioms LatinonEntropy.measurable_finiteIndependentKernel_event
