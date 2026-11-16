module

public import WeightedLogSum
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

noncomputable section

namespace LatinonEntropy

open Finset
open scoped Classical

def finiteImageFiber {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (f : I → A) (a : A) : Finset I := T.filter (fun x => f x = a)

def uniformImageWeight {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (f : I → A) (a : A) : ℝ :=
  ((finiteImageFiber T f a).card : ℝ)/(T.card : ℝ)

theorem uniform_image_moment {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (f : I → A) (F : A → ℝ) :
    (∑ a ∈ T.image f, uniformImageWeight T f a*F a) =
      (∑ x ∈ T, F (f x))/(T.card : ℝ) := by
  have hs : (∑ a ∈ T.image f, ((finiteImageFiber T f a).card : ℝ)*F a) =
      ∑ x ∈ T, F (f x) := by
    have h := sum_by_coordinate T f (fun a (_ : I) => F a)
    simpa only [finiteImageFiber,sum_const,nsmul_eq_mul] using h.symm
  calc
    _ = ∑ a ∈ T.image f, (((finiteImageFiber T f a).card : ℝ)*F a)/(T.card : ℝ) := by
      apply sum_congr rfl
      intro a _
      unfold uniformImageWeight
      ring
    _ = _ := by rw [← sum_div,hs]

theorem uniformImageWeight_nonneg {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (f : I → A) (a : A) : 0 ≤ uniformImageWeight T f a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem uniformImageWeight_pos {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (hT : T.Nonempty) (f : I → A) (a : A) (ha : a ∈ T.image f) :
    0 < uniformImageWeight T f a := by
  obtain ⟨x,hx,hfx⟩ := mem_image.mp ha
  have hfiber : (finiteImageFiber T f a).Nonempty := by
    refine ⟨x,?_⟩
    simp only [finiteImageFiber,mem_filter]
    exact ⟨hx,hfx⟩
  exact div_pos (Nat.cast_pos.mpr (card_pos.mpr hfiber)) (Nat.cast_pos.mpr (card_pos.mpr hT))

theorem uniformImageWeight_total {I A : Type*} [DecidableEq I] [DecidableEq A]
    (T : Finset I) (hT : T.Nonempty) (f : I → A) :
    (∑ a ∈ T.image f, uniformImageWeight T f a) = 1 := by
  have hn : (0 : ℝ) < T.card := Nat.cast_pos.mpr (card_pos.mpr hT)
  simpa [hn.ne'] using uniform_image_moment T f (fun _ => (1 : ℝ))

end LatinonEntropy

#print axioms LatinonEntropy.uniform_image_moment
#print axioms LatinonEntropy.uniformImageWeight_pos
#print axioms LatinonEntropy.uniformImageWeight_total
