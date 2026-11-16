module

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Finite definition/proof source cut from cdr-palomar-kernel and its pinned vendors;
see series_cdr_provenance.json. The absorption existence library is not imported.
-/
public import Mathlib
public import SeriesCDR.Basic
public import HistoryLatinArray

@[expose] public section

noncomputable section
open Finset
open scoped Classical

namespace TypedTriangle
structure Host (V I : Type*) where
  G : SimpleGraph V
  lab : V → I

variable {V I : Type*} [Fintype V]

/-- `E(T)`: las aristas (pares no diagonales) de un conjunto de vértices `T`. -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

/-- Las aristas del host como `Finset`. -/
def edges (H : Host V I) : Finset (Sym2 V) := univ.filter (fun e => e ∈ H.G.edgeSet)

/-- Triángulo permitido: tres vértices distintos, mutuamente adyacentes, cuyo multiconjunto
de etiquetas está en `F`. -/
def IsAllowed (H : Host V I) (F : Set (Multiset I)) (T : Finset V) : Prop :=
  T.card = 3 ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → H.G.Adj x y) ∧ T.val.map H.lab ∈ F


end TypedTriangle

namespace STS
variable {α : Type*} [DecidableEq α]
def IsSTS (B : Finset (Finset α)) : Prop :=
  (∀ A ∈ B, A.card = 3) ∧ ∀ x y : α, x ≠ y → ∃! A, A ∈ B ∧ x ∈ A ∧ y ∈ A

def IsLatin {n : ℕ} (l : Fin n → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (l i)) ∧ ∀ j, Function.Bijective (fun i => l i j)


end STS

namespace CDRBicolour.Prefix
def col3 (a b c : ℕ) (v : Fin (a + b + c)) : Fin 3 :=
  if v.val < a then 0 else if v.val < a + b then 1 else 2


end CDRBicolour.Prefix
namespace CDRBicolour.Absorption
open TypedTriangle CDRBicolour.Prefix
def cdrF : Set (Multiset (Fin 3)) := {m | Multiset.card m = 3 ∧ m.toFinset.card = 2}

/-- The CDR host of a profile. -/
def cdrHost (a b c : ℕ) : Host (Fin (a + b + c)) (Fin 3) := ⟨⊤, col3 a b c⟩

def cHost {V : Type*} (lab : V → Fin 3) : Host V (Fin 3) := ⟨⊤,lab⟩

variable {V I : Type*} [DecidableEq V]
theorem val_map_triple (lab : V → I) {u v z : V} (huv : u ≠ v) (hzu : z ≠ u) (hzv : z ≠ v) :
    (({u, v, z} : Finset V).val.map lab) = ({lab u, lab v, lab z} : Multiset I) := by
  have h1 : v ∉ ({z} : Finset V) := by simp [Ne.symm hzv]
  have h2 : u ∉ ({v, z} : Finset V) := by simp [huv, Ne.symm hzu]
  rw [insert_val_of_notMem h2, insert_val_of_notMem h1]
  simp

theorem isAllowed_triple (lab : V → Fin 3) {x y z : V} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hF : ({lab x, lab y, lab z} : Multiset (Fin 3)) ∈ cdrF) :
    IsAllowed (cHost lab) cdrF {x, y, z} := by
  refine ⟨card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, fun u _ v _ huv => ?_, ?_⟩
  · simpa [cHost] using huv
  · change ({x,y,z} : Finset V).val.map lab ∈ cdrF
    rw [val_map_triple lab hxy (Ne.symm hxz) (Ne.symm hyz)]; exact hF


end CDRBicolour.Absorption
