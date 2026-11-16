module

public import FiniteCore
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

@[expose] public section

/-! Weighted directed walks and bounded potentials for the correction lemma.
No-negative-closed-walk and short-path hypotheses are stated explicitly.
The optimizer-to-no-negative-walk and cut-to-short-path implications remain
separate obligations; they are not assumed to have been formalized here. -/

noncomputable section

namespace LatinonEntropy

variable {V : Type*}

inductive CostWalk (R : V → V → Prop) (c : V → V → ℝ) (a : V) : V → ℝ → ℕ → Prop
  | nil : CostWalk R c a a 0 0
  | snoc {b : V} {t : ℝ} {n : ℕ} (walk : CostWalk R c a b t n)
      {d : V} (edge : R b d) : CostWalk R c a d (t + c b d) (n + 1)

namespace CostWalk

theorem append {R : V → V → Prop} {c : V → V → ℝ}
    {a b d : V} {s t : ℝ} {m n : ℕ}
    (p : CostWalk R c a b s m) (q : CostWalk R c b d t n) :
    CostWalk R c a d (s + t) (m + n) := by
  induction q with
  | nil => simpa using p
  | snoc q edge ih => simpa [add_assoc] using ih.snoc edge

theorem potential_le {R : V → V → Prop} {c : V → V → ℝ}
    (phi : V → ℝ) (hedge : ∀ u v, R u v → phi v - phi u ≤ c u v)
    {a b : V} {t : ℝ} {n : ℕ} (p : CostWalk R c a b t n) :
    phi b - phi a ≤ t := by
  induction p with
  | nil => simp
  | snoc p edge ih =>
      have h := hedge _ _ edge
      linarith

theorem cost_le_length {R : V → V → Prop} {c : V → V → ℝ}
    (hcost : ∀ u v, R u v → c u v ≤ 1)
    {a b : V} {t : ℝ} {n : ℕ} (p : CostWalk R c a b t n) : t ≤ n := by
  induction p with
  | nil => simp
  | snoc p edge ih =>
      have h := hcost _ _ edge
      push_cast
      linarith

end CostWalk

/-- Infima of walk costs construct a feasible potential. Return paths and
nonnegative closed walks bound each set of forward costs below. No finite
enumeration of simple paths or cycle extraction is needed for this step. -/
theorem exists_potential_of_closed_walks
    (R : V → V → Prop) (c : V → V → ℝ) (root : V)
    (hreach : ∀ u v, ∃ t n, CostWalk R c u v t n)
    (hclosed : ∀ v t n, CostWalk R c v v t n → 0 ≤ t) :
    ∃ phi : V → ℝ, ∀ u v, R u v → phi v - phi u ≤ c u v := by
  let costs : V → Set ℝ := fun v => {t | ∃ n, CostWalk R c root v t n}
  have hne : ∀ v, (costs v).Nonempty := by
    intro v
    obtain ⟨t, n, ht⟩ := hreach root v
    exact ⟨t, n, ht⟩
  have hbdd : ∀ v, BddBelow (costs v) := by
    intro v
    obtain ⟨b, k, back⟩ := hreach v root
    refine ⟨-b, ?_⟩
    intro t ht
    obtain ⟨n, forward⟩ := ht
    have h := hclosed root (t + b) (n + k) (forward.append back)
    linarith
  let phi : V → ℝ := fun v => sInf (costs v)
  refine ⟨phi, ?_⟩
  intro u v edge
  have h : phi v - c u v ≤ phi u := by
    apply le_csInf (hne u)
    intro t ht
    obtain ⟨n, p⟩ := ht
    have hle : phi v ≤ t + c u v := csInf_le (hbdd v) ⟨n + 1, p.snoc edge⟩
    linarith
  linarith

/-- Oscillation at most six allows a shift placing all potentials in [-3,3]. -/
theorem exists_bounded_potential
    [Finite V] [Nonempty V] (R : V → V → Prop) (c : V → V → ℝ)
    (hcost : ∀ u v, R u v → c u v ≤ 1)
    (hdiam : ∀ u v, ∃ t n, CostWalk R c u v t n ∧ n ≤ 6)
    (hclosed : ∀ v t n, CostWalk R c v v t n → 0 ≤ t) :
    ∃ phi : V → ℝ, (∀ v, |phi v| ≤ 3) ∧
      ∀ u v, R u v → phi v - phi u ≤ c u v := by
  classical
  have hreach : ∀ u v, ∃ t n, CostWalk R c u v t n := by
    intro u v
    obtain ⟨t, n, hp, _⟩ := hdiam u v
    exact ⟨t, n, hp⟩
  obtain ⟨psi, hpsi⟩ := exists_potential_of_closed_walks R c
    (Classical.arbitrary V) hreach hclosed
  obtain ⟨v0, hmin⟩ := Finite.exists_min psi
  refine ⟨fun v => psi v - psi v0 - 3, ?_, ?_⟩
  · intro v
    obtain ⟨t, n, hp, hn⟩ := hdiam v0 v
    have h1 := hp.potential_le psi hpsi
    have h2 := hp.cost_le_length hcost
    have h3 : (n : ℝ) ≤ 6 := by exact_mod_cast hn
    have h0 := hmin v
    apply abs_le.mpr
    constructor <;> linarith
  · intro u v edge
    have h := hpsi u v edge
    dsimp
    linarith

/-- Existence of graph potentials supplies the matrix correction cost bound.
The graph and its no-negative-closed-walk/diameter properties remain explicit. -/
theorem correction_cost_of_residual_graph
    {Y Z : Type*} [Fintype Y] [Fintype Z] [Nonempty Y]
    (M Q : Y → Z → ℝ) (R : Y ⊕ Z → Y ⊕ Z → Prop)
    (c : Y ⊕ Z → Y ⊕ Z → ℝ)
    (hrow : ∀ y, ∑ z, Q y z = 1) (hcol : ∀ z, ∑ y, Q y z = 1)
    (hcost : ∀ u v, R u v → c u v ≤ 1)
    (hdiam : ∀ u v, ∃ t n, CostWalk R c u v t n ∧ n ≤ 6)
    (hclosed : ∀ v t n, CostWalk R c v v t n → 0 ≤ t)
    (hup : ∀ y z, Q y z < M y z →
      R (.inl y) (.inr z) ∧ c (.inl y) (.inr z) ≤ -1)
    (hdown : ∀ y z, M y z < Q y z →
      R (.inr z) (.inl y) ∧ c (.inr z) (.inl y) ≤ -1) :
    (∑ y, ∑ z, |Q y z - M y z|) ≤
      3 * ((∑ y, |(∑ z, M y z) - 1|) + ∑ z, |(∑ y, M y z) - 1|) := by
  obtain ⟨phi, hbound, hedge⟩ := exists_bounded_potential R c hcost hdiam hclosed
  apply correction_cost_unit_margins M Q (fun y => phi (.inl y))
    (fun z => phi (.inr z)) (fun y => hbound _) (fun z => hbound _) hrow hcol
  · intro y z h
    obtain ⟨he, hc⟩ := hup y z h
    exact (hedge _ _ he).trans hc
  · intro y z h
    obtain ⟨he, hc⟩ := hdown y z h
    have hh := (hedge _ _ he).trans hc
    linarith

end LatinonEntropy

#print axioms LatinonEntropy.exists_bounded_potential
#print axioms LatinonEntropy.correction_cost_of_residual_graph
