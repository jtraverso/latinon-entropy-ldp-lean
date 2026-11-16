module

public import Mathlib

@[expose] public section

noncomputable section

namespace LatinonEntropy

open MeasureTheory Function
open scoped Classical unitInterval

def kernelGraphProduct {V : Type*} (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (x : V → I) : ℝ := ∏ e ∈ E, K e (x e.1,x e.2)

def edgeIncident {V : Type*} (u : V) (e : V × V) : Prop := e.1=u ∨ e.2=u

/-- An orientation of a simple graph, expressed without choosing an ordering of vertices. -/
def NoOppositeEdges {V : Type*} (E : Finset (V × V)) : Prop := ∀ e ∈ E, e.swap ∉ E

theorem noOppositeEdges_distinct {V : Type*} (E : Finset (V × V)) (hE : NoOppositeEdges E)
    (a : V × V) (ha : a ∈ E) : a.1 ≠ a.2 := by
  intro h
  have heq : a.swap=a := Prod.ext h.symm h
  apply hE a ha
  rwa [heq]

theorem noOppositeEdges_erased_separate {V : Type*} [DecidableEq V]
    (E : Finset (V × V)) (hE : NoOppositeEdges E) (a : V × V) (ha : a ∈ E) :
    ∀ e ∈ E.erase a, edgeIncident a.1 e → ¬edgeIncident a.2 e := by
  intro e he hu hv
  obtain ⟨hne,heE⟩ := Finset.mem_erase.mp he
  have hdist := noOppositeEdges_distinct E hE a ha
  rcases hu with hu|hu
  · rcases hv with hv|hv
    · exact hdist (hu.symm.trans hv)
    · exact hne (Prod.ext hu hv)
  · rcases hv with hv|hv
    · apply hE a ha
      have heq : e=a.swap := Prod.ext hv hu
      rwa [← heq]
    · exact hdist (hu.symm.trans hv)

theorem measurable_kernelGraphProduct {V : Type*} (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ E, Measurable (K e)) :
    Measurable (kernelGraphProduct E K) :=
  Finset.measurable_fun_prod E (fun e he => (hK e he).comp
    ((measurable_pi_apply e.1).prodMk (measurable_pi_apply e.2)))

theorem kernelGraphProduct_mem_Icc {V : Type*} (E : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ E, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1)
    (x : V → I) : kernelGraphProduct E K x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun e he => (hK e he _).1)
  · exact Finset.prod_le_one₀ (fun e he => (hK e he _).1) (fun e he => (hK e he _).2)

def edgeProductLeft {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (u : V) (r : V → I) (a : I) : ℝ :=
  kernelGraphProduct (S.filter (edgeIncident u)) K (update r u a)

def edgeProductRight {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (u v : V) (r : V → I) (b : I) : ℝ :=
  kernelGraphProduct (S.filter (fun e => ¬edgeIncident u e)) K (update r v b)

theorem measurable_edgeProductLeft {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ S, Measurable (K e)) (u : V) (r : V → I) :
    Measurable (edgeProductLeft S K u r) :=
  (measurable_kernelGraphProduct _ K (fun e he => hK e (Finset.mem_filter.mp he).1)).comp (measurable_update r)

theorem measurable_edgeProductRight {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ S, Measurable (K e)) (u v : V) (r : V → I) :
    Measurable (edgeProductRight S K u v r) :=
  (measurable_kernelGraphProduct _ K (fun e he => hK e (Finset.mem_filter.mp he).1)).comp (measurable_update r)

theorem edgeProductLeft_mem_Icc {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ S, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1)
    (u : V) (r : V → I) (a : I) : edgeProductLeft S K u r a ∈ Set.Icc (0 : ℝ) 1 :=
  kernelGraphProduct_mem_Icc _ K (fun e he => hK e (Finset.mem_filter.mp he).1) _

theorem edgeProductRight_mem_Icc {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (hK : ∀ e ∈ S, ∀ p, K e p ∈ Set.Icc (0 : ℝ) 1)
    (u v : V) (r : V → I) (b : I) : edgeProductRight S K u v r b ∈ Set.Icc (0 : ℝ) 1 :=
  kernelGraphProduct_mem_Icc _ K (fun e he => hK e (Finset.mem_filter.mp he).1) _

/-- With no other edge joining the selected vertices, the remaining
product separates into one weight for each of the two fresh coordinates. -/
theorem kernelGraphProduct_separate {V : Type*} [DecidableEq V] (S : Finset (V × V))
    (K : (V × V) → I × I → ℝ) (u v : V) (huv : u ≠ v)
    (hsep : ∀ e ∈ S, edgeIncident u e → ¬edgeIncident v e)
    (r : V → I) (a b : I) :
    kernelGraphProduct S K (update (update r u a) v b)=
      edgeProductLeft S K u r a*edgeProductRight S K u v r b := by
  unfold kernelGraphProduct edgeProductLeft edgeProductRight
  rw [← Finset.prod_filter_mul_prod_filter_not S (edgeIncident u)]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    obtain ⟨heS,heu⟩ := Finset.mem_filter.mp he
    have hev := hsep e heS heu
    have h1 : e.1 ≠ v := fun h => hev (Or.inl h)
    have h2 : e.2 ≠ v := fun h => hev (Or.inr h)
    simp only [update_of_ne h1,update_of_ne h2]
  · apply Finset.prod_congr rfl
    intro e he
    have heu := (Finset.mem_filter.mp he).2
    have h1 : e.1 ≠ u := fun h => heu (Or.inl h)
    have h2 : e.2 ≠ u := fun h => heu (Or.inr h)
    rw [update_comm huv]
    simp only [update_of_ne h1,update_of_ne h2]

end LatinonEntropy

#print axioms LatinonEntropy.noOppositeEdges_distinct
#print axioms LatinonEntropy.noOppositeEdges_erased_separate
#print axioms LatinonEntropy.measurable_kernelGraphProduct
#print axioms LatinonEntropy.kernelGraphProduct_mem_Icc
#print axioms LatinonEntropy.measurable_edgeProductLeft
#print axioms LatinonEntropy.measurable_edgeProductRight
#print axioms LatinonEntropy.edgeProductLeft_mem_Icc
#print axioms LatinonEntropy.edgeProductRight_mem_Icc
#print axioms LatinonEntropy.kernelGraphProduct_separate
