module

public import Mathlib

@[expose] public section

noncomputable section

namespace LatinonEntropy

open scoped Classical

/-- An order pattern assigns every rank exactly once to a rectangular cell. -/
abbrev LatinOrderPattern (k l : ℕ) := (Fin k × Fin l) ≃ Fin (k*l)

/-- Realizations have the strict relative order prescribed by the pattern.
In particular all cell values must be distinct. -/
def orderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    Set ((Fin k × Fin l) → ℝ) :=
  {v | ∀ a b, P a < P b → v a < v b}

theorem mem_orderPatternRealizations_iff {k l : ℕ} (P : LatinOrderPattern k l)
    (v : (Fin k × Fin l) → ℝ) :
    v ∈ orderPatternRealizations P ↔ ∀ a b, v a < v b ↔ P a < P b := by
  constructor
  · intro hv a b
    constructor
    · intro hab
      rcases lt_trichotomy (P a) (P b) with hp | hp | hp
      · exact hp
      · have he : a=b := P.injective hp
        subst b
        exact False.elim (lt_irrefl _ hab)
      · exact False.elim (lt_asymm hab (hv b a hp))
    · exact hv a b
  · intro hv a b hab
    exact (hv a b).mpr hab

theorem orderPatternRealizations_injective {k l : ℕ} (P : LatinOrderPattern k l)
    (v : (Fin k × Fin l) → ℝ) (hv : v ∈ orderPatternRealizations P) :
    Function.Injective v := by
  intro a b hab
  apply P.injective
  rcases lt_trichotomy (P a) (P b) with hp | hp | hp
  · have h := hv a b hp
    rw [hab] at h
    exact False.elim (lt_irrefl _ h)
  · exact hp
  · have h := hv b a hp
    rw [hab] at h
    exact False.elim (lt_irrefl _ h)

theorem isOpen_orderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    IsOpen (orderPatternRealizations P) := by
  unfold orderPatternRealizations
  simp only [Set.ofPred_forall]
  refine isOpen_iInter_of_finite (fun a => ?_)
  refine isOpen_iInter_of_finite (fun b => ?_)
  refine isOpen_iInter_of_finite (fun _ => ?_)
  exact isOpen_lt (continuous_apply a) (continuous_apply b)

theorem measurableSet_orderPatternRealizations {k l : ℕ} (P : LatinOrderPattern k l) :
    MeasurableSet (orderPatternRealizations P) := (isOpen_orderPatternRealizations P).measurableSet

theorem orderPatternRealizations_strictMono {k l : ℕ} (P : LatinOrderPattern k l)
    (v : (Fin k × Fin l) → ℝ) (psi : ℝ → ℝ) (hpsi : StrictMono psi) :
    (fun a => psi (v a)) ∈ orderPatternRealizations P ↔ v ∈ orderPatternRealizations P := by
  constructor
  · intro hv a b hab
    exact hpsi.lt_iff_lt.mp (hv a b hab)
  · intro hv a b hab
    exact hpsi (hv a b hab)

end LatinonEntropy

#print axioms LatinonEntropy.mem_orderPatternRealizations_iff
#print axioms LatinonEntropy.orderPatternRealizations_injective
#print axioms LatinonEntropy.isOpen_orderPatternRealizations
#print axioms LatinonEntropy.measurableSet_orderPatternRealizations
#print axioms LatinonEntropy.orderPatternRealizations_strictMono
